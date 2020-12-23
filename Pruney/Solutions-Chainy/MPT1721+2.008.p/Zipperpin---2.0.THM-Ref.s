%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pL3neZW67R

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:31 EST 2020

% Result     : Theorem 21.65s
% Output     : Refutation 21.65s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 150 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   23
%              Number of atoms          :  976 (3088 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X14 )
      | ( r1_tarski @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
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

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( r1_tsep_1 @ X5 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X6 )
      | ( X8
       != ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( ( u1_struct_0 @ X8 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) @ X6 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X6 @ X5 @ X7 ) )
      | ( r1_tsep_1 @ X5 @ X7 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
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
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
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
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
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
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('41',plain,
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
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X14 ) )
      | ( m1_pre_topc @ X12 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
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
    inference('sup-',[status(thm)],['21','48'])).

thf('50',plain,
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
    inference('sup-',[status(thm)],['7','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pL3neZW67R
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 21.65/21.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 21.65/21.87  % Solved by: fo/fo7.sh
% 21.65/21.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.65/21.87  % done 3498 iterations in 21.414s
% 21.65/21.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 21.65/21.87  % SZS output start Refutation
% 21.65/21.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 21.65/21.87  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 21.65/21.87  thf(sk_B_type, type, sk_B: $i).
% 21.65/21.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 21.65/21.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 21.65/21.87  thf(sk_C_type, type, sk_C: $i).
% 21.65/21.87  thf(sk_A_type, type, sk_A: $i).
% 21.65/21.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.65/21.87  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 21.65/21.87  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 21.65/21.87  thf(sk_D_type, type, sk_D: $i).
% 21.65/21.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 21.65/21.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 21.65/21.87  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 21.65/21.87  thf(t30_tmap_1, conjecture,
% 21.65/21.87    (![A:$i]:
% 21.65/21.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 21.65/21.87       ( ![B:$i]:
% 21.65/21.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 21.65/21.87           ( ![C:$i]:
% 21.65/21.87             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 21.65/21.87               ( ![D:$i]:
% 21.65/21.87                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 21.65/21.87                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 21.65/21.87                     ( ( r1_tsep_1 @ B @ C ) | 
% 21.65/21.87                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 21.65/21.87  thf(zf_stmt_0, negated_conjecture,
% 21.65/21.87    (~( ![A:$i]:
% 21.65/21.87        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 21.65/21.87            ( l1_pre_topc @ A ) ) =>
% 21.65/21.87          ( ![B:$i]:
% 21.65/21.87            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 21.65/21.87              ( ![C:$i]:
% 21.65/21.87                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 21.65/21.87                  ( ![D:$i]:
% 21.65/21.87                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 21.65/21.87                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 21.65/21.87                        ( ( r1_tsep_1 @ B @ C ) | 
% 21.65/21.87                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 21.65/21.87    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 21.65/21.87  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf(dt_k2_tsep_1, axiom,
% 21.65/21.87    (![A:$i,B:$i,C:$i]:
% 21.65/21.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 21.65/21.87         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 21.65/21.87         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 21.65/21.87       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 21.65/21.87         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 21.65/21.87         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 21.65/21.87  thf('3', plain,
% 21.65/21.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 21.65/21.87         (~ (m1_pre_topc @ X9 @ X10)
% 21.65/21.87          | (v2_struct_0 @ X9)
% 21.65/21.87          | ~ (l1_pre_topc @ X10)
% 21.65/21.87          | (v2_struct_0 @ X10)
% 21.65/21.87          | (v2_struct_0 @ X11)
% 21.65/21.87          | ~ (m1_pre_topc @ X11 @ X10)
% 21.65/21.87          | (m1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 21.65/21.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 21.65/21.87  thf('4', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 21.65/21.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ X0)
% 21.65/21.87          | (v2_struct_0 @ sk_A)
% 21.65/21.87          | ~ (l1_pre_topc @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ sk_B))),
% 21.65/21.87      inference('sup-', [status(thm)], ['2', '3'])).
% 21.65/21.87  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('6', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 21.65/21.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ X0)
% 21.65/21.87          | (v2_struct_0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ sk_B))),
% 21.65/21.87      inference('demod', [status(thm)], ['4', '5'])).
% 21.65/21.87  thf('7', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 21.65/21.87      inference('sup-', [status(thm)], ['1', '6'])).
% 21.65/21.87  thf('8', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf(t4_tsep_1, axiom,
% 21.65/21.87    (![A:$i]:
% 21.65/21.87     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 21.65/21.87       ( ![B:$i]:
% 21.65/21.87         ( ( m1_pre_topc @ B @ A ) =>
% 21.65/21.87           ( ![C:$i]:
% 21.65/21.87             ( ( m1_pre_topc @ C @ A ) =>
% 21.65/21.87               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 21.65/21.87                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 21.65/21.87  thf('10', plain,
% 21.65/21.87      (![X12 : $i, X13 : $i, X14 : $i]:
% 21.65/21.87         (~ (m1_pre_topc @ X12 @ X13)
% 21.65/21.87          | ~ (m1_pre_topc @ X12 @ X14)
% 21.65/21.87          | (r1_tarski @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X14))
% 21.65/21.87          | ~ (m1_pre_topc @ X14 @ X13)
% 21.65/21.87          | ~ (l1_pre_topc @ X13)
% 21.65/21.87          | ~ (v2_pre_topc @ X13))),
% 21.65/21.87      inference('cnf', [status(esa)], [t4_tsep_1])).
% 21.65/21.87  thf('11', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         (~ (v2_pre_topc @ sk_A)
% 21.65/21.87          | ~ (l1_pre_topc @ sk_A)
% 21.65/21.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 21.65/21.87          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 21.65/21.87          | ~ (m1_pre_topc @ sk_B @ X0))),
% 21.65/21.87      inference('sup-', [status(thm)], ['9', '10'])).
% 21.65/21.87  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('14', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         (~ (m1_pre_topc @ X0 @ sk_A)
% 21.65/21.87          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 21.65/21.87          | ~ (m1_pre_topc @ sk_B @ X0))),
% 21.65/21.87      inference('demod', [status(thm)], ['11', '12', '13'])).
% 21.65/21.87  thf('15', plain,
% 21.65/21.87      ((~ (m1_pre_topc @ sk_B @ sk_D)
% 21.65/21.87        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))),
% 21.65/21.87      inference('sup-', [status(thm)], ['8', '14'])).
% 21.65/21.87  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('17', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))),
% 21.65/21.87      inference('demod', [status(thm)], ['15', '16'])).
% 21.65/21.87  thf(t17_xboole_1, axiom,
% 21.65/21.87    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 21.65/21.87  thf('18', plain,
% 21.65/21.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 21.65/21.87      inference('cnf', [status(esa)], [t17_xboole_1])).
% 21.65/21.87  thf(t1_xboole_1, axiom,
% 21.65/21.87    (![A:$i,B:$i,C:$i]:
% 21.65/21.87     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 21.65/21.87       ( r1_tarski @ A @ C ) ))).
% 21.65/21.87  thf('19', plain,
% 21.65/21.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 21.65/21.87         (~ (r1_tarski @ X2 @ X3)
% 21.65/21.87          | ~ (r1_tarski @ X3 @ X4)
% 21.65/21.87          | (r1_tarski @ X2 @ X4))),
% 21.65/21.87      inference('cnf', [status(esa)], [t1_xboole_1])).
% 21.65/21.87  thf('20', plain,
% 21.65/21.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.65/21.87         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 21.65/21.87      inference('sup-', [status(thm)], ['18', '19'])).
% 21.65/21.87  thf('21', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         (r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ X0) @ 
% 21.65/21.87          (u1_struct_0 @ sk_D))),
% 21.65/21.87      inference('sup-', [status(thm)], ['17', '20'])).
% 21.65/21.87  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('24', plain,
% 21.65/21.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 21.65/21.87         (~ (m1_pre_topc @ X9 @ X10)
% 21.65/21.87          | (v2_struct_0 @ X9)
% 21.65/21.87          | ~ (l1_pre_topc @ X10)
% 21.65/21.87          | (v2_struct_0 @ X10)
% 21.65/21.87          | (v2_struct_0 @ X11)
% 21.65/21.87          | ~ (m1_pre_topc @ X11 @ X10)
% 21.65/21.87          | (v1_pre_topc @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 21.65/21.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 21.65/21.87  thf('25', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 21.65/21.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ X0)
% 21.65/21.87          | (v2_struct_0 @ sk_A)
% 21.65/21.87          | ~ (l1_pre_topc @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ sk_B))),
% 21.65/21.87      inference('sup-', [status(thm)], ['23', '24'])).
% 21.65/21.87  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('27', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 21.65/21.87          | ~ (m1_pre_topc @ X0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ X0)
% 21.65/21.87          | (v2_struct_0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ sk_B))),
% 21.65/21.87      inference('demod', [status(thm)], ['25', '26'])).
% 21.65/21.87  thf('28', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 21.65/21.87      inference('sup-', [status(thm)], ['22', '27'])).
% 21.65/21.87  thf('29', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 21.65/21.87      inference('sup-', [status(thm)], ['1', '6'])).
% 21.65/21.87  thf(d5_tsep_1, axiom,
% 21.65/21.87    (![A:$i]:
% 21.65/21.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 21.65/21.87       ( ![B:$i]:
% 21.65/21.87         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 21.65/21.87           ( ![C:$i]:
% 21.65/21.87             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 21.65/21.87               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 21.65/21.87                 ( ![D:$i]:
% 21.65/21.87                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 21.65/21.87                       ( m1_pre_topc @ D @ A ) ) =>
% 21.65/21.87                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 21.65/21.87                       ( ( u1_struct_0 @ D ) =
% 21.65/21.87                         ( k3_xboole_0 @
% 21.65/21.87                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 21.65/21.87  thf('30', plain,
% 21.65/21.87      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 21.65/21.87         ((v2_struct_0 @ X5)
% 21.65/21.87          | ~ (m1_pre_topc @ X5 @ X6)
% 21.65/21.87          | (r1_tsep_1 @ X5 @ X7)
% 21.65/21.87          | (v2_struct_0 @ X8)
% 21.65/21.87          | ~ (v1_pre_topc @ X8)
% 21.65/21.87          | ~ (m1_pre_topc @ X8 @ X6)
% 21.65/21.87          | ((X8) != (k2_tsep_1 @ X6 @ X5 @ X7))
% 21.65/21.87          | ((u1_struct_0 @ X8)
% 21.65/21.87              = (k3_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X7)))
% 21.65/21.87          | ~ (m1_pre_topc @ X7 @ X6)
% 21.65/21.87          | (v2_struct_0 @ X7)
% 21.65/21.87          | ~ (l1_pre_topc @ X6)
% 21.65/21.87          | (v2_struct_0 @ X6))),
% 21.65/21.87      inference('cnf', [status(esa)], [d5_tsep_1])).
% 21.65/21.87  thf('31', plain,
% 21.65/21.87      (![X5 : $i, X6 : $i, X7 : $i]:
% 21.65/21.87         ((v2_struct_0 @ X6)
% 21.65/21.87          | ~ (l1_pre_topc @ X6)
% 21.65/21.87          | (v2_struct_0 @ X7)
% 21.65/21.87          | ~ (m1_pre_topc @ X7 @ X6)
% 21.65/21.87          | ((u1_struct_0 @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 21.65/21.87              = (k3_xboole_0 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X7)))
% 21.65/21.87          | ~ (m1_pre_topc @ (k2_tsep_1 @ X6 @ X5 @ X7) @ X6)
% 21.65/21.87          | ~ (v1_pre_topc @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 21.65/21.87          | (v2_struct_0 @ (k2_tsep_1 @ X6 @ X5 @ X7))
% 21.65/21.87          | (r1_tsep_1 @ X5 @ X7)
% 21.65/21.87          | ~ (m1_pre_topc @ X5 @ X6)
% 21.65/21.87          | (v2_struct_0 @ X5))),
% 21.65/21.87      inference('simplify', [status(thm)], ['30'])).
% 21.65/21.87  thf('32', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 21.65/21.87        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | ~ (l1_pre_topc @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_A))),
% 21.65/21.87      inference('sup-', [status(thm)], ['29', '31'])).
% 21.65/21.87  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('36', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A))),
% 21.65/21.87      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 21.65/21.87  thf('37', plain,
% 21.65/21.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 21.65/21.87        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C))),
% 21.65/21.87      inference('simplify', [status(thm)], ['36'])).
% 21.65/21.87  thf('38', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 21.65/21.87      inference('sup-', [status(thm)], ['28', '37'])).
% 21.65/21.87  thf('39', plain,
% 21.65/21.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 21.65/21.87        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C))),
% 21.65/21.87      inference('simplify', [status(thm)], ['38'])).
% 21.65/21.87  thf('40', plain,
% 21.65/21.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 21.65/21.87         (~ (m1_pre_topc @ X9 @ X10)
% 21.65/21.87          | (v2_struct_0 @ X9)
% 21.65/21.87          | ~ (l1_pre_topc @ X10)
% 21.65/21.87          | (v2_struct_0 @ X10)
% 21.65/21.87          | (v2_struct_0 @ X11)
% 21.65/21.87          | ~ (m1_pre_topc @ X11 @ X10)
% 21.65/21.87          | ~ (v2_struct_0 @ (k2_tsep_1 @ X10 @ X9 @ X11)))),
% 21.65/21.87      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 21.65/21.87  thf('41', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 21.65/21.87        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | ~ (l1_pre_topc @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 21.65/21.87      inference('sup-', [status(thm)], ['39', '40'])).
% 21.65/21.87  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('44', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('45', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B))),
% 21.65/21.87      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 21.65/21.87  thf('46', plain,
% 21.65/21.87      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 21.65/21.87          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C))),
% 21.65/21.87      inference('simplify', [status(thm)], ['45'])).
% 21.65/21.87  thf('47', plain,
% 21.65/21.87      (![X12 : $i, X13 : $i, X14 : $i]:
% 21.65/21.87         (~ (m1_pre_topc @ X12 @ X13)
% 21.65/21.87          | ~ (r1_tarski @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X14))
% 21.65/21.87          | (m1_pre_topc @ X12 @ X14)
% 21.65/21.87          | ~ (m1_pre_topc @ X14 @ X13)
% 21.65/21.87          | ~ (l1_pre_topc @ X13)
% 21.65/21.87          | ~ (v2_pre_topc @ X13))),
% 21.65/21.87      inference('cnf', [status(esa)], [t4_tsep_1])).
% 21.65/21.87  thf('48', plain,
% 21.65/21.87      (![X0 : $i, X1 : $i]:
% 21.65/21.87         (~ (r1_tarski @ 
% 21.65/21.87             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 21.65/21.87             (u1_struct_0 @ X0))
% 21.65/21.87          | (v2_struct_0 @ sk_C)
% 21.65/21.87          | (v2_struct_0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ sk_B)
% 21.65/21.87          | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87          | ~ (v2_pre_topc @ X1)
% 21.65/21.87          | ~ (l1_pre_topc @ X1)
% 21.65/21.87          | ~ (m1_pre_topc @ X0 @ X1)
% 21.65/21.87          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 21.65/21.87          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 21.65/21.87      inference('sup-', [status(thm)], ['46', '47'])).
% 21.65/21.87  thf('49', plain,
% 21.65/21.87      (![X0 : $i]:
% 21.65/21.87         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 21.65/21.87          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 21.65/21.87          | ~ (m1_pre_topc @ sk_D @ X0)
% 21.65/21.87          | ~ (l1_pre_topc @ X0)
% 21.65/21.87          | ~ (v2_pre_topc @ X0)
% 21.65/21.87          | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87          | (v2_struct_0 @ sk_B)
% 21.65/21.87          | (v2_struct_0 @ sk_A)
% 21.65/21.87          | (v2_struct_0 @ sk_C))),
% 21.65/21.87      inference('sup-', [status(thm)], ['21', '48'])).
% 21.65/21.87  thf('50', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | ~ (v2_pre_topc @ sk_A)
% 21.65/21.87        | ~ (l1_pre_topc @ sk_A)
% 21.65/21.87        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 21.65/21.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 21.65/21.87      inference('sup-', [status(thm)], ['7', '49'])).
% 21.65/21.87  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('53', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('54', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 21.65/21.87      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 21.65/21.87  thf('55', plain,
% 21.65/21.87      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_C))),
% 21.65/21.87      inference('simplify', [status(thm)], ['54'])).
% 21.65/21.87  thf('56', plain, (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('57', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_C)
% 21.65/21.87        | (v2_struct_0 @ sk_A)
% 21.65/21.87        | (v2_struct_0 @ sk_B)
% 21.65/21.87        | (r1_tsep_1 @ sk_B @ sk_C))),
% 21.65/21.87      inference('sup-', [status(thm)], ['55', '56'])).
% 21.65/21.87  thf('58', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('59', plain,
% 21.65/21.87      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 21.65/21.87      inference('sup-', [status(thm)], ['57', '58'])).
% 21.65/21.87  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('61', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 21.65/21.87      inference('clc', [status(thm)], ['59', '60'])).
% 21.65/21.87  thf('62', plain, (~ (v2_struct_0 @ sk_C)),
% 21.65/21.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.65/21.87  thf('63', plain, ((v2_struct_0 @ sk_A)),
% 21.65/21.87      inference('clc', [status(thm)], ['61', '62'])).
% 21.65/21.87  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 21.65/21.87  
% 21.65/21.87  % SZS output end Refutation
% 21.65/21.87  
% 21.65/21.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
