%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i6D7k7aQP2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:31 EST 2020

% Result     : Theorem 5.35s
% Output     : Refutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 139 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  971 (2781 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t30_tmap_1,conjecture,(
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
                 => ( ( ( m1_pre_topc @ B @ D )
                      & ( m1_pre_topc @ C @ D ) )
                   => ( ( r1_tsep_1 @ B @ C )
                      | ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) )).

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
                   => ( ( ( m1_pre_topc @ B @ D )
                        & ( m1_pre_topc @ C @ D ) )
                     => ( ( r1_tsep_1 @ B @ C )
                        | ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( m1_pre_topc @ X12 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X9 )
      | ( r1_tsep_1 @ X7 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X8 @ X7 @ X10 ) @ ( k2_tsep_1 @ X8 @ X9 @ X11 ) )
      | ~ ( m1_pre_topc @ X11 @ X8 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_tmap_1])).

thf('6',plain,(
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
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
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
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_A @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_A @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_A @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_A @ sk_D ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_A @ sk_D ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( m1_pre_topc @ X12 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

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

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( r1_tsep_1 @ X13 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X13 )
      | ( ( k2_tsep_1 @ X14 @ X13 @ X15 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_tsep_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( k2_tsep_1 @ X0 @ X0 @ X1 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X0 @ X1 )
      | ( ( k2_tsep_1 @ X0 @ X0 @ X1 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( ( k2_tsep_1 @ sk_A @ sk_A @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( r1_tsep_1 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( ( k2_tsep_1 @ sk_A @ sk_A @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( r1_tsep_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ( m1_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k2_tsep_1 @ sk_A @ sk_A @ sk_D ) )
      | ( r1_tsep_1 @ sk_A @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_D )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k2_tsep_1 @ sk_A @ sk_A @ sk_D ) )
      | ( r1_tsep_1 @ sk_A @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,
    ( ( r1_tsep_1 @ sk_A @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( m1_pre_topc @ X12 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
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

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X4 @ X6 )
      | ~ ( r1_tsep_1 @ X6 @ X4 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t22_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ~ ( r1_tsep_1 @ sk_A @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( r1_tsep_1 @ sk_A @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r1_tsep_1 @ sk_A @ sk_D )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( r1_tsep_1 @ sk_A @ sk_D ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ~ ( r1_tsep_1 @ sk_A @ sk_D ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','55'])).

thf('57',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i6D7k7aQP2
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 5.35/5.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.35/5.56  % Solved by: fo/fo7.sh
% 5.35/5.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.35/5.56  % done 4296 iterations in 5.092s
% 5.35/5.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.35/5.56  % SZS output start Refutation
% 5.35/5.56  thf(sk_C_type, type, sk_C: $i).
% 5.35/5.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 5.35/5.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 5.35/5.56  thf(sk_A_type, type, sk_A: $i).
% 5.35/5.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.35/5.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.35/5.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.35/5.56  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 5.35/5.56  thf(sk_D_type, type, sk_D: $i).
% 5.35/5.56  thf(sk_B_type, type, sk_B: $i).
% 5.35/5.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 5.35/5.56  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 5.35/5.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.35/5.56  thf(t30_tmap_1, conjecture,
% 5.35/5.56    (![A:$i]:
% 5.35/5.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.35/5.56       ( ![B:$i]:
% 5.35/5.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.35/5.56           ( ![C:$i]:
% 5.35/5.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.35/5.56               ( ![D:$i]:
% 5.35/5.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.35/5.56                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 5.35/5.56                     ( ( r1_tsep_1 @ B @ C ) | 
% 5.35/5.56                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 5.35/5.56  thf(zf_stmt_0, negated_conjecture,
% 5.35/5.56    (~( ![A:$i]:
% 5.35/5.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.35/5.56            ( l1_pre_topc @ A ) ) =>
% 5.35/5.56          ( ![B:$i]:
% 5.35/5.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.35/5.56              ( ![C:$i]:
% 5.35/5.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.35/5.56                  ( ![D:$i]:
% 5.35/5.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.35/5.56                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 5.35/5.56                        ( ( r1_tsep_1 @ B @ C ) | 
% 5.35/5.56                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 5.35/5.56    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 5.35/5.56  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf(t2_tsep_1, axiom,
% 5.35/5.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 5.35/5.56  thf('2', plain,
% 5.35/5.56      (![X12 : $i]: ((m1_pre_topc @ X12 @ X12) | ~ (l1_pre_topc @ X12))),
% 5.35/5.56      inference('cnf', [status(esa)], [t2_tsep_1])).
% 5.35/5.56  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf(t28_tmap_1, axiom,
% 5.35/5.56    (![A:$i]:
% 5.35/5.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.35/5.56       ( ![B:$i]:
% 5.35/5.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.35/5.56           ( ![C:$i]:
% 5.35/5.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.35/5.56               ( ![D:$i]:
% 5.35/5.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.35/5.56                   ( ![E:$i]:
% 5.35/5.56                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 5.35/5.56                       ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 5.35/5.56                         ( ( r1_tsep_1 @ B @ C ) | 
% 5.35/5.56                           ( m1_pre_topc @
% 5.35/5.56                             ( k2_tsep_1 @ A @ B @ C ) @ 
% 5.35/5.56                             ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.35/5.56  thf('5', plain,
% 5.35/5.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 5.35/5.56         ((v2_struct_0 @ X7)
% 5.35/5.56          | ~ (m1_pre_topc @ X7 @ X8)
% 5.35/5.56          | (v2_struct_0 @ X9)
% 5.35/5.56          | ~ (m1_pre_topc @ X9 @ X8)
% 5.35/5.56          | ~ (m1_pre_topc @ X7 @ X9)
% 5.35/5.56          | (r1_tsep_1 @ X7 @ X10)
% 5.35/5.56          | ~ (m1_pre_topc @ X10 @ X11)
% 5.35/5.56          | (m1_pre_topc @ (k2_tsep_1 @ X8 @ X7 @ X10) @ 
% 5.35/5.56             (k2_tsep_1 @ X8 @ X9 @ X11))
% 5.35/5.56          | ~ (m1_pre_topc @ X11 @ X8)
% 5.35/5.56          | (v2_struct_0 @ X11)
% 5.35/5.56          | ~ (m1_pre_topc @ X10 @ X8)
% 5.35/5.56          | (v2_struct_0 @ X10)
% 5.35/5.56          | ~ (l1_pre_topc @ X8)
% 5.35/5.56          | ~ (v2_pre_topc @ X8)
% 5.35/5.56          | (v2_struct_0 @ X8))),
% 5.35/5.56      inference('cnf', [status(esa)], [t28_tmap_1])).
% 5.35/5.56  thf('6', plain,
% 5.35/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.35/5.56         ((v2_struct_0 @ sk_A)
% 5.35/5.56          | ~ (v2_pre_topc @ sk_A)
% 5.35/5.56          | ~ (l1_pre_topc @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X1)
% 5.35/5.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 5.35/5.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 5.35/5.56             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ X1)
% 5.35/5.56          | (r1_tsep_1 @ sk_B @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_B @ X2)
% 5.35/5.56          | ~ (m1_pre_topc @ X2 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X2)
% 5.35/5.56          | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('sup-', [status(thm)], ['4', '5'])).
% 5.35/5.56  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('9', plain,
% 5.35/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.35/5.56         ((v2_struct_0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X1)
% 5.35/5.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 5.35/5.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 5.35/5.56             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ X1)
% 5.35/5.56          | (r1_tsep_1 @ sk_B @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_B @ X2)
% 5.35/5.56          | ~ (m1_pre_topc @ X2 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X2)
% 5.35/5.56          | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('demod', [status(thm)], ['6', '7', '8'])).
% 5.35/5.56  thf('10', plain,
% 5.35/5.56      (![X0 : $i, X1 : $i]:
% 5.35/5.56         ((v2_struct_0 @ sk_B)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_B @ X0)
% 5.35/5.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 5.35/5.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 5.35/5.56             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 5.35/5.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X1)
% 5.35/5.56          | (v2_struct_0 @ sk_C)
% 5.35/5.56          | (v2_struct_0 @ sk_A))),
% 5.35/5.56      inference('sup-', [status(thm)], ['3', '9'])).
% 5.35/5.56  thf('11', plain,
% 5.35/5.56      (![X0 : $i]:
% 5.35/5.56         (~ (l1_pre_topc @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ sk_C)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 5.35/5.56             (k2_tsep_1 @ sk_A @ sk_A @ X0))
% 5.35/5.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 5.35/5.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('sup-', [status(thm)], ['2', '10'])).
% 5.35/5.56  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('14', plain,
% 5.35/5.56      (![X0 : $i]:
% 5.35/5.56         ((v2_struct_0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ sk_C)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 5.35/5.56             (k2_tsep_1 @ sk_A @ sk_A @ X0))
% 5.35/5.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 5.35/5.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56          | (v2_struct_0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('demod', [status(thm)], ['11', '12', '13'])).
% 5.35/5.56  thf('15', plain,
% 5.35/5.56      (![X0 : $i]:
% 5.35/5.56         ((v2_struct_0 @ sk_B)
% 5.35/5.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 5.35/5.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 5.35/5.56             (k2_tsep_1 @ sk_A @ sk_A @ X0))
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | (v2_struct_0 @ sk_C)
% 5.35/5.56          | (v2_struct_0 @ sk_A))),
% 5.35/5.56      inference('simplify', [status(thm)], ['14'])).
% 5.35/5.56  thf('16', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 5.35/5.56        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 5.35/5.56           (k2_tsep_1 @ sk_A @ sk_A @ sk_D))
% 5.35/5.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('sup-', [status(thm)], ['1', '15'])).
% 5.35/5.56  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('18', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 5.35/5.56           (k2_tsep_1 @ sk_A @ sk_A @ sk_D))
% 5.35/5.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('demod', [status(thm)], ['16', '17'])).
% 5.35/5.56  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('20', plain,
% 5.35/5.56      (![X12 : $i]: ((m1_pre_topc @ X12 @ X12) | ~ (l1_pre_topc @ X12))),
% 5.35/5.56      inference('cnf', [status(esa)], [t2_tsep_1])).
% 5.35/5.56  thf(t31_tsep_1, axiom,
% 5.35/5.56    (![A:$i]:
% 5.35/5.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.35/5.56       ( ![B:$i]:
% 5.35/5.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.35/5.56           ( ![C:$i]:
% 5.35/5.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.35/5.56               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 5.35/5.56                 ( ( ( m1_pre_topc @ B @ C ) =>
% 5.35/5.56                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 5.35/5.56                       ( g1_pre_topc @
% 5.35/5.56                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 5.35/5.56                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 5.35/5.56                       ( g1_pre_topc @
% 5.35/5.56                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 5.35/5.56                     ( m1_pre_topc @ B @ C ) ) & 
% 5.35/5.56                   ( ( m1_pre_topc @ C @ B ) =>
% 5.35/5.56                     ( ( k2_tsep_1 @ A @ B @ C ) =
% 5.35/5.56                       ( g1_pre_topc @
% 5.35/5.56                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) & 
% 5.35/5.56                   ( ( ( k2_tsep_1 @ A @ B @ C ) =
% 5.35/5.56                       ( g1_pre_topc @
% 5.35/5.56                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 5.35/5.56                     ( m1_pre_topc @ C @ B ) ) ) ) ) ) ) ) ))).
% 5.35/5.56  thf('21', plain,
% 5.35/5.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.35/5.56         ((v2_struct_0 @ X13)
% 5.35/5.56          | ~ (m1_pre_topc @ X13 @ X14)
% 5.35/5.56          | (r1_tsep_1 @ X13 @ X15)
% 5.35/5.56          | ~ (m1_pre_topc @ X15 @ X13)
% 5.35/5.56          | ((k2_tsep_1 @ X14 @ X13 @ X15)
% 5.35/5.56              = (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 5.35/5.56          | ~ (m1_pre_topc @ X15 @ X14)
% 5.35/5.56          | (v2_struct_0 @ X15)
% 5.35/5.56          | ~ (l1_pre_topc @ X14)
% 5.35/5.56          | ~ (v2_pre_topc @ X14)
% 5.35/5.56          | (v2_struct_0 @ X14))),
% 5.35/5.56      inference('cnf', [status(esa)], [t31_tsep_1])).
% 5.35/5.56  thf('22', plain,
% 5.35/5.56      (![X0 : $i, X1 : $i]:
% 5.35/5.56         (~ (l1_pre_topc @ X0)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (v2_pre_topc @ X0)
% 5.35/5.56          | ~ (l1_pre_topc @ X0)
% 5.35/5.56          | (v2_struct_0 @ X1)
% 5.35/5.56          | ~ (m1_pre_topc @ X1 @ X0)
% 5.35/5.56          | ((k2_tsep_1 @ X0 @ X0 @ X1)
% 5.35/5.56              = (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 5.35/5.56          | ~ (m1_pre_topc @ X1 @ X0)
% 5.35/5.56          | (r1_tsep_1 @ X0 @ X1)
% 5.35/5.56          | (v2_struct_0 @ X0))),
% 5.35/5.56      inference('sup-', [status(thm)], ['20', '21'])).
% 5.35/5.56  thf('23', plain,
% 5.35/5.56      (![X0 : $i, X1 : $i]:
% 5.35/5.56         ((r1_tsep_1 @ X0 @ X1)
% 5.35/5.56          | ((k2_tsep_1 @ X0 @ X0 @ X1)
% 5.35/5.56              = (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 5.35/5.56          | ~ (m1_pre_topc @ X1 @ X0)
% 5.35/5.56          | (v2_struct_0 @ X1)
% 5.35/5.56          | ~ (v2_pre_topc @ X0)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (l1_pre_topc @ X0))),
% 5.35/5.56      inference('simplify', [status(thm)], ['22'])).
% 5.35/5.56  thf('24', plain,
% 5.35/5.56      ((~ (l1_pre_topc @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_A)
% 5.35/5.56        | ~ (v2_pre_topc @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | ((k2_tsep_1 @ sk_A @ sk_A @ sk_D)
% 5.35/5.56            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 5.35/5.56        | (r1_tsep_1 @ sk_A @ sk_D))),
% 5.35/5.56      inference('sup-', [status(thm)], ['19', '23'])).
% 5.35/5.56  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('27', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | ((k2_tsep_1 @ sk_A @ sk_A @ sk_D)
% 5.35/5.56            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 5.35/5.56        | (r1_tsep_1 @ sk_A @ sk_D))),
% 5.35/5.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 5.35/5.56  thf(t59_pre_topc, axiom,
% 5.35/5.56    (![A:$i]:
% 5.35/5.56     ( ( l1_pre_topc @ A ) =>
% 5.35/5.56       ( ![B:$i]:
% 5.35/5.56         ( ( m1_pre_topc @
% 5.35/5.56             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 5.35/5.56           ( m1_pre_topc @ B @ A ) ) ) ))).
% 5.35/5.56  thf('28', plain,
% 5.35/5.56      (![X2 : $i, X3 : $i]:
% 5.35/5.56         (~ (m1_pre_topc @ X2 @ 
% 5.35/5.56             (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 5.35/5.56          | (m1_pre_topc @ X2 @ X3)
% 5.35/5.56          | ~ (l1_pre_topc @ X3))),
% 5.35/5.56      inference('cnf', [status(esa)], [t59_pre_topc])).
% 5.35/5.56  thf('29', plain,
% 5.35/5.56      (![X0 : $i]:
% 5.35/5.56         (~ (m1_pre_topc @ X0 @ (k2_tsep_1 @ sk_A @ sk_A @ sk_D))
% 5.35/5.56          | (r1_tsep_1 @ sk_A @ sk_D)
% 5.35/5.56          | (v2_struct_0 @ sk_D)
% 5.35/5.56          | (v2_struct_0 @ sk_A)
% 5.35/5.56          | ~ (l1_pre_topc @ sk_D)
% 5.35/5.56          | (m1_pre_topc @ X0 @ sk_D))),
% 5.35/5.56      inference('sup-', [status(thm)], ['27', '28'])).
% 5.35/5.56  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf(dt_m1_pre_topc, axiom,
% 5.35/5.56    (![A:$i]:
% 5.35/5.56     ( ( l1_pre_topc @ A ) =>
% 5.35/5.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 5.35/5.56  thf('31', plain,
% 5.35/5.56      (![X0 : $i, X1 : $i]:
% 5.35/5.56         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 5.35/5.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.35/5.56  thf('32', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 5.35/5.56      inference('sup-', [status(thm)], ['30', '31'])).
% 5.35/5.56  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('34', plain, ((l1_pre_topc @ sk_D)),
% 5.35/5.56      inference('demod', [status(thm)], ['32', '33'])).
% 5.35/5.56  thf('35', plain,
% 5.35/5.56      (![X0 : $i]:
% 5.35/5.56         (~ (m1_pre_topc @ X0 @ (k2_tsep_1 @ sk_A @ sk_A @ sk_D))
% 5.35/5.56          | (r1_tsep_1 @ sk_A @ sk_D)
% 5.35/5.56          | (v2_struct_0 @ sk_D)
% 5.35/5.56          | (v2_struct_0 @ sk_A)
% 5.35/5.56          | (m1_pre_topc @ X0 @ sk_D))),
% 5.35/5.56      inference('demod', [status(thm)], ['29', '34'])).
% 5.35/5.56  thf('36', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_B)
% 5.35/5.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_A)
% 5.35/5.56        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | (r1_tsep_1 @ sk_A @ sk_D))),
% 5.35/5.56      inference('sup-', [status(thm)], ['18', '35'])).
% 5.35/5.56  thf('37', plain,
% 5.35/5.56      (((r1_tsep_1 @ sk_A @ sk_D)
% 5.35/5.56        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('simplify', [status(thm)], ['36'])).
% 5.35/5.56  thf('38', plain, (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('39', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_B)
% 5.35/5.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_A)
% 5.35/5.56        | (r1_tsep_1 @ sk_A @ sk_D))),
% 5.35/5.56      inference('sup-', [status(thm)], ['37', '38'])).
% 5.35/5.56  thf('40', plain,
% 5.35/5.56      (![X12 : $i]: ((m1_pre_topc @ X12 @ X12) | ~ (l1_pre_topc @ X12))),
% 5.35/5.56      inference('cnf', [status(esa)], [t2_tsep_1])).
% 5.35/5.56  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf(t22_tmap_1, axiom,
% 5.35/5.56    (![A:$i]:
% 5.35/5.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.35/5.56       ( ![B:$i]:
% 5.35/5.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.35/5.56           ( ![C:$i]:
% 5.35/5.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.35/5.56               ( ( m1_pre_topc @ B @ C ) =>
% 5.35/5.56                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 5.35/5.56  thf('42', plain,
% 5.35/5.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.35/5.56         ((v2_struct_0 @ X4)
% 5.35/5.56          | ~ (m1_pre_topc @ X4 @ X5)
% 5.35/5.56          | ~ (m1_pre_topc @ X4 @ X6)
% 5.35/5.56          | ~ (r1_tsep_1 @ X6 @ X4)
% 5.35/5.56          | ~ (m1_pre_topc @ X6 @ X5)
% 5.35/5.56          | (v2_struct_0 @ X6)
% 5.35/5.56          | ~ (l1_pre_topc @ X5)
% 5.35/5.56          | ~ (v2_pre_topc @ X5)
% 5.35/5.56          | (v2_struct_0 @ X5))),
% 5.35/5.56      inference('cnf', [status(esa)], [t22_tmap_1])).
% 5.35/5.56  thf('43', plain,
% 5.35/5.56      (![X0 : $i]:
% 5.35/5.56         ((v2_struct_0 @ sk_A)
% 5.35/5.56          | ~ (v2_pre_topc @ sk_A)
% 5.35/5.56          | ~ (l1_pre_topc @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | ~ (r1_tsep_1 @ X0 @ sk_D)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 5.35/5.56          | (v2_struct_0 @ sk_D))),
% 5.35/5.56      inference('sup-', [status(thm)], ['41', '42'])).
% 5.35/5.56  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('46', plain,
% 5.35/5.56      (![X0 : $i]:
% 5.35/5.56         ((v2_struct_0 @ sk_A)
% 5.35/5.56          | (v2_struct_0 @ X0)
% 5.35/5.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.35/5.56          | ~ (r1_tsep_1 @ X0 @ sk_D)
% 5.35/5.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 5.35/5.56          | (v2_struct_0 @ sk_D))),
% 5.35/5.56      inference('demod', [status(thm)], ['43', '44', '45'])).
% 5.35/5.56  thf('47', plain,
% 5.35/5.56      ((~ (l1_pre_topc @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 5.35/5.56        | ~ (r1_tsep_1 @ sk_A @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_A))),
% 5.35/5.56      inference('sup-', [status(thm)], ['40', '46'])).
% 5.35/5.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('50', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_D)
% 5.35/5.56        | ~ (r1_tsep_1 @ sk_A @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_A))),
% 5.35/5.56      inference('demod', [status(thm)], ['47', '48', '49'])).
% 5.35/5.56  thf('51', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_A)
% 5.35/5.56        | ~ (r1_tsep_1 @ sk_A @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_D))),
% 5.35/5.56      inference('simplify', [status(thm)], ['50'])).
% 5.35/5.56  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('53', plain, (((v2_struct_0 @ sk_D) | ~ (r1_tsep_1 @ sk_A @ sk_D))),
% 5.35/5.56      inference('clc', [status(thm)], ['51', '52'])).
% 5.35/5.56  thf('54', plain, (~ (v2_struct_0 @ sk_D)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('55', plain, (~ (r1_tsep_1 @ sk_A @ sk_D)),
% 5.35/5.56      inference('clc', [status(thm)], ['53', '54'])).
% 5.35/5.56  thf('56', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_A)
% 5.35/5.56        | (v2_struct_0 @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | (r1_tsep_1 @ sk_B @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('sup-', [status(thm)], ['39', '55'])).
% 5.35/5.56  thf('57', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('58', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_B)
% 5.35/5.56        | (v2_struct_0 @ sk_D)
% 5.35/5.56        | (v2_struct_0 @ sk_C)
% 5.35/5.56        | (v2_struct_0 @ sk_A))),
% 5.35/5.56      inference('sup-', [status(thm)], ['56', '57'])).
% 5.35/5.56  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('60', plain,
% 5.35/5.56      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 5.35/5.56      inference('sup-', [status(thm)], ['58', '59'])).
% 5.35/5.56  thf('61', plain, (~ (v2_struct_0 @ sk_C)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('62', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 5.35/5.56      inference('clc', [status(thm)], ['60', '61'])).
% 5.35/5.56  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 5.35/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.56  thf('64', plain, ((v2_struct_0 @ sk_D)),
% 5.35/5.56      inference('clc', [status(thm)], ['62', '63'])).
% 5.35/5.56  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 5.35/5.56  
% 5.35/5.56  % SZS output end Refutation
% 5.35/5.56  
% 5.35/5.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
