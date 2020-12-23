%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lb92uFNrnR

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:31 EST 2020

% Result     : Theorem 16.35s
% Output     : Refutation 16.35s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 147 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   23
%              Number of atoms          :  956 (3068 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
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
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_pre_topc @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( D
                        = ( k2_tsep_1 @ A @ B @ C ) )
                    <=> ( ( u1_struct_0 @ D )
                        = ( k3_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( r1_tsep_1 @ X3 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X4 )
      | ( X6
       != ( k2_tsep_1 @ X4 @ X3 @ X5 ) )
      | ( ( u1_struct_0 @ X6 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) @ X4 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X4 @ X3 @ X5 ) )
      | ( r1_tsep_1 @ X3 @ X5 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ( m1_pre_topc @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['7','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lb92uFNrnR
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:32:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 16.35/16.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 16.35/16.54  % Solved by: fo/fo7.sh
% 16.35/16.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.35/16.54  % done 1978 iterations in 16.037s
% 16.35/16.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 16.35/16.54  % SZS output start Refutation
% 16.35/16.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 16.35/16.54  thf(sk_A_type, type, sk_A: $i).
% 16.35/16.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 16.35/16.54  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 16.35/16.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 16.35/16.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 16.35/16.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.35/16.54  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 16.35/16.54  thf(sk_C_type, type, sk_C: $i).
% 16.35/16.54  thf(sk_D_type, type, sk_D: $i).
% 16.35/16.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 16.35/16.54  thf(sk_B_type, type, sk_B: $i).
% 16.35/16.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 16.35/16.54  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 16.35/16.54  thf(t30_tmap_1, conjecture,
% 16.35/16.54    (![A:$i]:
% 16.35/16.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.35/16.54       ( ![B:$i]:
% 16.35/16.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 16.35/16.54           ( ![C:$i]:
% 16.35/16.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 16.35/16.54               ( ![D:$i]:
% 16.35/16.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 16.35/16.54                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 16.35/16.54                     ( ( r1_tsep_1 @ B @ C ) | 
% 16.35/16.54                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 16.35/16.54  thf(zf_stmt_0, negated_conjecture,
% 16.35/16.54    (~( ![A:$i]:
% 16.35/16.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 16.35/16.54            ( l1_pre_topc @ A ) ) =>
% 16.35/16.54          ( ![B:$i]:
% 16.35/16.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 16.35/16.54              ( ![C:$i]:
% 16.35/16.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 16.35/16.54                  ( ![D:$i]:
% 16.35/16.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 16.35/16.54                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 16.35/16.54                        ( ( r1_tsep_1 @ B @ C ) | 
% 16.35/16.54                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 16.35/16.54    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 16.35/16.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf(dt_k2_tsep_1, axiom,
% 16.35/16.54    (![A:$i,B:$i,C:$i]:
% 16.35/16.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 16.35/16.54         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 16.35/16.54         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 16.35/16.54       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 16.35/16.54         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 16.35/16.54         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 16.35/16.54  thf('3', plain,
% 16.35/16.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 16.35/16.54         (~ (m1_pre_topc @ X7 @ X8)
% 16.35/16.54          | (v2_struct_0 @ X7)
% 16.35/16.54          | ~ (l1_pre_topc @ X8)
% 16.35/16.54          | (v2_struct_0 @ X8)
% 16.35/16.54          | (v2_struct_0 @ X9)
% 16.35/16.54          | ~ (m1_pre_topc @ X9 @ X8)
% 16.35/16.54          | (m1_pre_topc @ (k2_tsep_1 @ X8 @ X7 @ X9) @ X8))),
% 16.35/16.54      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 16.35/16.54  thf('4', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 16.35/16.54          | ~ (m1_pre_topc @ X0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ X0)
% 16.35/16.54          | (v2_struct_0 @ sk_A)
% 16.35/16.54          | ~ (l1_pre_topc @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ sk_B))),
% 16.35/16.54      inference('sup-', [status(thm)], ['2', '3'])).
% 16.35/16.54  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('6', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 16.35/16.54          | ~ (m1_pre_topc @ X0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ X0)
% 16.35/16.54          | (v2_struct_0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ sk_B))),
% 16.35/16.54      inference('demod', [status(thm)], ['4', '5'])).
% 16.35/16.54  thf('7', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 16.35/16.54      inference('sup-', [status(thm)], ['1', '6'])).
% 16.35/16.54  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf(t4_tsep_1, axiom,
% 16.35/16.54    (![A:$i]:
% 16.35/16.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.35/16.54       ( ![B:$i]:
% 16.35/16.54         ( ( m1_pre_topc @ B @ A ) =>
% 16.35/16.54           ( ![C:$i]:
% 16.35/16.54             ( ( m1_pre_topc @ C @ A ) =>
% 16.35/16.54               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 16.35/16.54                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 16.35/16.54  thf('10', plain,
% 16.35/16.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 16.35/16.54         (~ (m1_pre_topc @ X10 @ X11)
% 16.35/16.54          | ~ (m1_pre_topc @ X10 @ X12)
% 16.35/16.54          | (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 16.35/16.54          | ~ (m1_pre_topc @ X12 @ X11)
% 16.35/16.54          | ~ (l1_pre_topc @ X11)
% 16.35/16.54          | ~ (v2_pre_topc @ X11))),
% 16.35/16.54      inference('cnf', [status(esa)], [t4_tsep_1])).
% 16.35/16.54  thf('11', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         (~ (v2_pre_topc @ sk_A)
% 16.35/16.54          | ~ (l1_pre_topc @ sk_A)
% 16.35/16.54          | ~ (m1_pre_topc @ X0 @ sk_A)
% 16.35/16.54          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 16.35/16.54          | ~ (m1_pre_topc @ sk_B @ X0))),
% 16.35/16.54      inference('sup-', [status(thm)], ['9', '10'])).
% 16.35/16.54  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('14', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         (~ (m1_pre_topc @ X0 @ sk_A)
% 16.35/16.54          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 16.35/16.54          | ~ (m1_pre_topc @ sk_B @ X0))),
% 16.35/16.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 16.35/16.54  thf('15', plain,
% 16.35/16.54      ((~ (m1_pre_topc @ sk_B @ sk_D)
% 16.35/16.54        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))),
% 16.35/16.54      inference('sup-', [status(thm)], ['8', '14'])).
% 16.35/16.54  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('17', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))),
% 16.35/16.54      inference('demod', [status(thm)], ['15', '16'])).
% 16.35/16.54  thf(t108_xboole_1, axiom,
% 16.35/16.54    (![A:$i,B:$i,C:$i]:
% 16.35/16.54     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 16.35/16.54  thf('18', plain,
% 16.35/16.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.35/16.54         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 16.35/16.54      inference('cnf', [status(esa)], [t108_xboole_1])).
% 16.35/16.54  thf('19', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ X0) @ 
% 16.35/16.54          (u1_struct_0 @ sk_D))),
% 16.35/16.54      inference('sup-', [status(thm)], ['17', '18'])).
% 16.35/16.54  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('22', plain,
% 16.35/16.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 16.35/16.54         (~ (m1_pre_topc @ X7 @ X8)
% 16.35/16.54          | (v2_struct_0 @ X7)
% 16.35/16.54          | ~ (l1_pre_topc @ X8)
% 16.35/16.54          | (v2_struct_0 @ X8)
% 16.35/16.54          | (v2_struct_0 @ X9)
% 16.35/16.54          | ~ (m1_pre_topc @ X9 @ X8)
% 16.35/16.54          | (v1_pre_topc @ (k2_tsep_1 @ X8 @ X7 @ X9)))),
% 16.35/16.54      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 16.35/16.54  thf('23', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 16.35/16.54          | ~ (m1_pre_topc @ X0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ X0)
% 16.35/16.54          | (v2_struct_0 @ sk_A)
% 16.35/16.54          | ~ (l1_pre_topc @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ sk_B))),
% 16.35/16.54      inference('sup-', [status(thm)], ['21', '22'])).
% 16.35/16.54  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('25', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 16.35/16.54          | ~ (m1_pre_topc @ X0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ X0)
% 16.35/16.54          | (v2_struct_0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ sk_B))),
% 16.35/16.54      inference('demod', [status(thm)], ['23', '24'])).
% 16.35/16.54  thf('26', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 16.35/16.54      inference('sup-', [status(thm)], ['20', '25'])).
% 16.35/16.54  thf('27', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 16.35/16.54      inference('sup-', [status(thm)], ['1', '6'])).
% 16.35/16.54  thf(d5_tsep_1, axiom,
% 16.35/16.54    (![A:$i]:
% 16.35/16.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 16.35/16.54       ( ![B:$i]:
% 16.35/16.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 16.35/16.54           ( ![C:$i]:
% 16.35/16.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 16.35/16.54               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 16.35/16.54                 ( ![D:$i]:
% 16.35/16.54                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 16.35/16.54                       ( m1_pre_topc @ D @ A ) ) =>
% 16.35/16.54                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 16.35/16.54                       ( ( u1_struct_0 @ D ) =
% 16.35/16.54                         ( k3_xboole_0 @
% 16.35/16.54                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 16.35/16.54  thf('28', plain,
% 16.35/16.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 16.35/16.54         ((v2_struct_0 @ X3)
% 16.35/16.54          | ~ (m1_pre_topc @ X3 @ X4)
% 16.35/16.54          | (r1_tsep_1 @ X3 @ X5)
% 16.35/16.54          | (v2_struct_0 @ X6)
% 16.35/16.54          | ~ (v1_pre_topc @ X6)
% 16.35/16.54          | ~ (m1_pre_topc @ X6 @ X4)
% 16.35/16.54          | ((X6) != (k2_tsep_1 @ X4 @ X3 @ X5))
% 16.35/16.54          | ((u1_struct_0 @ X6)
% 16.35/16.54              = (k3_xboole_0 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X5)))
% 16.35/16.54          | ~ (m1_pre_topc @ X5 @ X4)
% 16.35/16.54          | (v2_struct_0 @ X5)
% 16.35/16.54          | ~ (l1_pre_topc @ X4)
% 16.35/16.54          | (v2_struct_0 @ X4))),
% 16.35/16.54      inference('cnf', [status(esa)], [d5_tsep_1])).
% 16.35/16.54  thf('29', plain,
% 16.35/16.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 16.35/16.54         ((v2_struct_0 @ X4)
% 16.35/16.54          | ~ (l1_pre_topc @ X4)
% 16.35/16.54          | (v2_struct_0 @ X5)
% 16.35/16.54          | ~ (m1_pre_topc @ X5 @ X4)
% 16.35/16.54          | ((u1_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5))
% 16.35/16.54              = (k3_xboole_0 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X5)))
% 16.35/16.54          | ~ (m1_pre_topc @ (k2_tsep_1 @ X4 @ X3 @ X5) @ X4)
% 16.35/16.54          | ~ (v1_pre_topc @ (k2_tsep_1 @ X4 @ X3 @ X5))
% 16.35/16.54          | (v2_struct_0 @ (k2_tsep_1 @ X4 @ X3 @ X5))
% 16.35/16.54          | (r1_tsep_1 @ X3 @ X5)
% 16.35/16.54          | ~ (m1_pre_topc @ X3 @ X4)
% 16.35/16.54          | (v2_struct_0 @ X3))),
% 16.35/16.54      inference('simplify', [status(thm)], ['28'])).
% 16.35/16.54  thf('30', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 16.35/16.54        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | ~ (l1_pre_topc @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_A))),
% 16.35/16.54      inference('sup-', [status(thm)], ['27', '29'])).
% 16.35/16.54  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('34', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A))),
% 16.35/16.54      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.35/16.54  thf('35', plain,
% 16.35/16.54      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 16.35/16.54        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C))),
% 16.35/16.54      inference('simplify', [status(thm)], ['34'])).
% 16.35/16.54  thf('36', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 16.35/16.54      inference('sup-', [status(thm)], ['26', '35'])).
% 16.35/16.54  thf('37', plain,
% 16.35/16.54      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 16.35/16.54        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C))),
% 16.35/16.54      inference('simplify', [status(thm)], ['36'])).
% 16.35/16.54  thf('38', plain,
% 16.35/16.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 16.35/16.54         (~ (m1_pre_topc @ X7 @ X8)
% 16.35/16.54          | (v2_struct_0 @ X7)
% 16.35/16.54          | ~ (l1_pre_topc @ X8)
% 16.35/16.54          | (v2_struct_0 @ X8)
% 16.35/16.54          | (v2_struct_0 @ X9)
% 16.35/16.54          | ~ (m1_pre_topc @ X9 @ X8)
% 16.35/16.54          | ~ (v2_struct_0 @ (k2_tsep_1 @ X8 @ X7 @ X9)))),
% 16.35/16.54      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 16.35/16.54  thf('39', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 16.35/16.54        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | ~ (l1_pre_topc @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 16.35/16.54      inference('sup-', [status(thm)], ['37', '38'])).
% 16.35/16.54  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('43', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B))),
% 16.35/16.54      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 16.35/16.54  thf('44', plain,
% 16.35/16.54      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 16.35/16.54          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C))),
% 16.35/16.54      inference('simplify', [status(thm)], ['43'])).
% 16.35/16.54  thf('45', plain,
% 16.35/16.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 16.35/16.54         (~ (m1_pre_topc @ X10 @ X11)
% 16.35/16.54          | ~ (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 16.35/16.54          | (m1_pre_topc @ X10 @ X12)
% 16.35/16.54          | ~ (m1_pre_topc @ X12 @ X11)
% 16.35/16.54          | ~ (l1_pre_topc @ X11)
% 16.35/16.54          | ~ (v2_pre_topc @ X11))),
% 16.35/16.54      inference('cnf', [status(esa)], [t4_tsep_1])).
% 16.35/16.54  thf('46', plain,
% 16.35/16.54      (![X0 : $i, X1 : $i]:
% 16.35/16.54         (~ (r1_tarski @ 
% 16.35/16.54             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 16.35/16.54             (u1_struct_0 @ X0))
% 16.35/16.54          | (v2_struct_0 @ sk_C)
% 16.35/16.54          | (v2_struct_0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ sk_B)
% 16.35/16.54          | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54          | ~ (v2_pre_topc @ X1)
% 16.35/16.54          | ~ (l1_pre_topc @ X1)
% 16.35/16.54          | ~ (m1_pre_topc @ X0 @ X1)
% 16.35/16.54          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 16.35/16.54          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 16.35/16.54      inference('sup-', [status(thm)], ['44', '45'])).
% 16.35/16.54  thf('47', plain,
% 16.35/16.54      (![X0 : $i]:
% 16.35/16.54         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 16.35/16.54          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 16.35/16.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 16.35/16.54          | ~ (l1_pre_topc @ X0)
% 16.35/16.54          | ~ (v2_pre_topc @ X0)
% 16.35/16.54          | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54          | (v2_struct_0 @ sk_B)
% 16.35/16.54          | (v2_struct_0 @ sk_A)
% 16.35/16.54          | (v2_struct_0 @ sk_C))),
% 16.35/16.54      inference('sup-', [status(thm)], ['19', '46'])).
% 16.35/16.54  thf('48', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | ~ (v2_pre_topc @ sk_A)
% 16.35/16.54        | ~ (l1_pre_topc @ sk_A)
% 16.35/16.54        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 16.35/16.54        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 16.35/16.54      inference('sup-', [status(thm)], ['7', '47'])).
% 16.35/16.54  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('51', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('52', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 16.35/16.54      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 16.35/16.54  thf('53', plain,
% 16.35/16.54      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_C))),
% 16.35/16.54      inference('simplify', [status(thm)], ['52'])).
% 16.35/16.54  thf('54', plain, (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('55', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_C)
% 16.35/16.54        | (v2_struct_0 @ sk_A)
% 16.35/16.54        | (v2_struct_0 @ sk_B)
% 16.35/16.54        | (r1_tsep_1 @ sk_B @ sk_C))),
% 16.35/16.54      inference('sup-', [status(thm)], ['53', '54'])).
% 16.35/16.54  thf('56', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('57', plain,
% 16.35/16.54      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 16.35/16.54      inference('sup-', [status(thm)], ['55', '56'])).
% 16.35/16.54  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('59', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 16.35/16.54      inference('clc', [status(thm)], ['57', '58'])).
% 16.35/16.54  thf('60', plain, (~ (v2_struct_0 @ sk_C)),
% 16.35/16.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.35/16.54  thf('61', plain, ((v2_struct_0 @ sk_A)),
% 16.35/16.54      inference('clc', [status(thm)], ['59', '60'])).
% 16.35/16.54  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 16.35/16.54  
% 16.35/16.54  % SZS output end Refutation
% 16.35/16.54  
% 16.35/16.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
