%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gO12nnbWYO

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:30 EST 2020

% Result     : Theorem 5.44s
% Output     : Refutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 164 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   22
%              Number of atoms          :  978 (3210 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t29_tmap_1,conjecture,(
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
                 => ( ( ( m1_pre_topc @ B @ C )
                      & ( m1_pre_topc @ D @ C ) )
                   => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) )).

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
                   => ( ( ( m1_pre_topc @ B @ C )
                        & ( m1_pre_topc @ D @ C ) )
                     => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
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
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
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
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
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
      | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( v1_pre_topc @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( X5
       != ( k1_tsep_1 @ X4 @ X3 @ X6 ) )
      | ( ( u1_struct_0 @ X5 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_pre_topc @ X6 @ X4 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X4 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X4 @ X3 @ X6 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X4 @ X3 @ X6 ) @ X4 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X4 @ X3 @ X6 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X4 @ X3 @ X6 ) )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ( m1_pre_topc @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gO12nnbWYO
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.44/5.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.44/5.61  % Solved by: fo/fo7.sh
% 5.44/5.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.44/5.61  % done 1503 iterations in 5.156s
% 5.44/5.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.44/5.61  % SZS output start Refutation
% 5.44/5.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 5.44/5.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.44/5.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.44/5.61  thf(sk_C_type, type, sk_C: $i).
% 5.44/5.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.44/5.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.44/5.61  thf(sk_B_type, type, sk_B: $i).
% 5.44/5.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.44/5.61  thf(sk_A_type, type, sk_A: $i).
% 5.44/5.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.44/5.61  thf(sk_D_type, type, sk_D: $i).
% 5.44/5.61  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 5.44/5.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 5.44/5.61  thf(t29_tmap_1, conjecture,
% 5.44/5.61    (![A:$i]:
% 5.44/5.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.44/5.61       ( ![B:$i]:
% 5.44/5.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.44/5.61           ( ![C:$i]:
% 5.44/5.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.44/5.61               ( ![D:$i]:
% 5.44/5.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.44/5.61                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 5.44/5.61                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 5.44/5.61  thf(zf_stmt_0, negated_conjecture,
% 5.44/5.61    (~( ![A:$i]:
% 5.44/5.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.44/5.61            ( l1_pre_topc @ A ) ) =>
% 5.44/5.61          ( ![B:$i]:
% 5.44/5.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.44/5.61              ( ![C:$i]:
% 5.44/5.61                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.44/5.61                  ( ![D:$i]:
% 5.44/5.61                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 5.44/5.61                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 5.44/5.61                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 5.44/5.61    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 5.44/5.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf(dt_k1_tsep_1, axiom,
% 5.44/5.61    (![A:$i,B:$i,C:$i]:
% 5.44/5.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 5.44/5.61         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 5.44/5.61         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.44/5.61       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 5.44/5.61         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 5.44/5.61         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 5.44/5.61  thf('3', plain,
% 5.44/5.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.44/5.61         (~ (m1_pre_topc @ X7 @ X8)
% 5.44/5.61          | (v2_struct_0 @ X7)
% 5.44/5.61          | ~ (l1_pre_topc @ X8)
% 5.44/5.61          | (v2_struct_0 @ X8)
% 5.44/5.61          | (v2_struct_0 @ X9)
% 5.44/5.61          | ~ (m1_pre_topc @ X9 @ X8)
% 5.44/5.61          | (m1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X9) @ X8))),
% 5.44/5.61      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 5.44/5.61  thf('4', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 5.44/5.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ X0)
% 5.44/5.61          | (v2_struct_0 @ sk_A)
% 5.44/5.61          | ~ (l1_pre_topc @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ sk_B))),
% 5.44/5.61      inference('sup-', [status(thm)], ['2', '3'])).
% 5.44/5.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('6', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 5.44/5.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ X0)
% 5.44/5.61          | (v2_struct_0 @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ sk_B))),
% 5.44/5.61      inference('demod', [status(thm)], ['4', '5'])).
% 5.44/5.61  thf('7', plain,
% 5.44/5.61      (((v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_D)
% 5.44/5.61        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 5.44/5.61      inference('sup-', [status(thm)], ['1', '6'])).
% 5.44/5.61  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf(t4_tsep_1, axiom,
% 5.44/5.61    (![A:$i]:
% 5.44/5.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.44/5.61       ( ![B:$i]:
% 5.44/5.61         ( ( m1_pre_topc @ B @ A ) =>
% 5.44/5.61           ( ![C:$i]:
% 5.44/5.61             ( ( m1_pre_topc @ C @ A ) =>
% 5.44/5.61               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 5.44/5.61                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 5.44/5.61  thf('10', plain,
% 5.44/5.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.44/5.61         (~ (m1_pre_topc @ X10 @ X11)
% 5.44/5.61          | ~ (m1_pre_topc @ X10 @ X12)
% 5.44/5.61          | (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 5.44/5.61          | ~ (m1_pre_topc @ X12 @ X11)
% 5.44/5.61          | ~ (l1_pre_topc @ X11)
% 5.44/5.61          | ~ (v2_pre_topc @ X11))),
% 5.44/5.61      inference('cnf', [status(esa)], [t4_tsep_1])).
% 5.44/5.61  thf('11', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         (~ (v2_pre_topc @ sk_A)
% 5.44/5.61          | ~ (l1_pre_topc @ sk_A)
% 5.44/5.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 5.44/5.61          | ~ (m1_pre_topc @ sk_D @ X0))),
% 5.44/5.61      inference('sup-', [status(thm)], ['9', '10'])).
% 5.44/5.61  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('14', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         (~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 5.44/5.61          | ~ (m1_pre_topc @ sk_D @ X0))),
% 5.44/5.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 5.44/5.61  thf('15', plain,
% 5.44/5.61      ((~ (m1_pre_topc @ sk_D @ sk_C)
% 5.44/5.61        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 5.44/5.61      inference('sup-', [status(thm)], ['8', '14'])).
% 5.44/5.61  thf('16', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('17', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 5.44/5.61      inference('demod', [status(thm)], ['15', '16'])).
% 5.44/5.61  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('20', plain,
% 5.44/5.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.44/5.61         (~ (m1_pre_topc @ X10 @ X11)
% 5.44/5.61          | ~ (m1_pre_topc @ X10 @ X12)
% 5.44/5.61          | (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 5.44/5.61          | ~ (m1_pre_topc @ X12 @ X11)
% 5.44/5.61          | ~ (l1_pre_topc @ X11)
% 5.44/5.61          | ~ (v2_pre_topc @ X11))),
% 5.44/5.61      inference('cnf', [status(esa)], [t4_tsep_1])).
% 5.44/5.61  thf('21', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         (~ (v2_pre_topc @ sk_A)
% 5.44/5.61          | ~ (l1_pre_topc @ sk_A)
% 5.44/5.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 5.44/5.61          | ~ (m1_pre_topc @ sk_B @ X0))),
% 5.44/5.61      inference('sup-', [status(thm)], ['19', '20'])).
% 5.44/5.61  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('24', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         (~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 5.44/5.61          | ~ (m1_pre_topc @ sk_B @ X0))),
% 5.44/5.61      inference('demod', [status(thm)], ['21', '22', '23'])).
% 5.44/5.61  thf('25', plain,
% 5.44/5.61      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 5.44/5.61        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 5.44/5.61      inference('sup-', [status(thm)], ['18', '24'])).
% 5.44/5.61  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('27', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 5.44/5.61      inference('demod', [status(thm)], ['25', '26'])).
% 5.44/5.61  thf(t8_xboole_1, axiom,
% 5.44/5.61    (![A:$i,B:$i,C:$i]:
% 5.44/5.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 5.44/5.61       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 5.44/5.61  thf('28', plain,
% 5.44/5.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.44/5.61         (~ (r1_tarski @ X0 @ X1)
% 5.44/5.61          | ~ (r1_tarski @ X2 @ X1)
% 5.44/5.61          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 5.44/5.61      inference('cnf', [status(esa)], [t8_xboole_1])).
% 5.44/5.61  thf('29', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         ((r1_tarski @ (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0) @ 
% 5.44/5.61           (u1_struct_0 @ sk_C))
% 5.44/5.61          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C)))),
% 5.44/5.61      inference('sup-', [status(thm)], ['27', '28'])).
% 5.44/5.61  thf('30', plain,
% 5.44/5.61      ((r1_tarski @ 
% 5.44/5.61        (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 5.44/5.61        (u1_struct_0 @ sk_C))),
% 5.44/5.61      inference('sup-', [status(thm)], ['17', '29'])).
% 5.44/5.61  thf('31', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('33', plain,
% 5.44/5.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.44/5.61         (~ (m1_pre_topc @ X7 @ X8)
% 5.44/5.61          | (v2_struct_0 @ X7)
% 5.44/5.61          | ~ (l1_pre_topc @ X8)
% 5.44/5.61          | (v2_struct_0 @ X8)
% 5.44/5.61          | (v2_struct_0 @ X9)
% 5.44/5.61          | ~ (m1_pre_topc @ X9 @ X8)
% 5.44/5.61          | (v1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X9)))),
% 5.44/5.61      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 5.44/5.61  thf('34', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 5.44/5.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ X0)
% 5.44/5.61          | (v2_struct_0 @ sk_A)
% 5.44/5.61          | ~ (l1_pre_topc @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ sk_B))),
% 5.44/5.61      inference('sup-', [status(thm)], ['32', '33'])).
% 5.44/5.61  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('36', plain,
% 5.44/5.61      (![X0 : $i]:
% 5.44/5.61         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 5.44/5.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ X0)
% 5.44/5.61          | (v2_struct_0 @ sk_A)
% 5.44/5.61          | (v2_struct_0 @ sk_B))),
% 5.44/5.61      inference('demod', [status(thm)], ['34', '35'])).
% 5.44/5.61  thf('37', plain,
% 5.44/5.61      (((v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_D)
% 5.44/5.61        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 5.44/5.61      inference('sup-', [status(thm)], ['31', '36'])).
% 5.44/5.61  thf('38', plain,
% 5.44/5.61      (((v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_D)
% 5.44/5.61        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_A))),
% 5.44/5.61      inference('sup-', [status(thm)], ['1', '6'])).
% 5.44/5.61  thf(d2_tsep_1, axiom,
% 5.44/5.61    (![A:$i]:
% 5.44/5.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 5.44/5.61       ( ![B:$i]:
% 5.44/5.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 5.44/5.61           ( ![C:$i]:
% 5.44/5.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.44/5.61               ( ![D:$i]:
% 5.44/5.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 5.44/5.61                     ( m1_pre_topc @ D @ A ) ) =>
% 5.44/5.61                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 5.44/5.61                     ( ( u1_struct_0 @ D ) =
% 5.44/5.61                       ( k2_xboole_0 @
% 5.44/5.61                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 5.44/5.61  thf('39', plain,
% 5.44/5.61      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.44/5.61         ((v2_struct_0 @ X3)
% 5.44/5.61          | ~ (m1_pre_topc @ X3 @ X4)
% 5.44/5.61          | (v2_struct_0 @ X5)
% 5.44/5.61          | ~ (v1_pre_topc @ X5)
% 5.44/5.61          | ~ (m1_pre_topc @ X5 @ X4)
% 5.44/5.61          | ((X5) != (k1_tsep_1 @ X4 @ X3 @ X6))
% 5.44/5.61          | ((u1_struct_0 @ X5)
% 5.44/5.61              = (k2_xboole_0 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X6)))
% 5.44/5.61          | ~ (m1_pre_topc @ X6 @ X4)
% 5.44/5.61          | (v2_struct_0 @ X6)
% 5.44/5.61          | ~ (l1_pre_topc @ X4)
% 5.44/5.61          | (v2_struct_0 @ X4))),
% 5.44/5.61      inference('cnf', [status(esa)], [d2_tsep_1])).
% 5.44/5.61  thf('40', plain,
% 5.44/5.61      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.44/5.61         ((v2_struct_0 @ X4)
% 5.44/5.61          | ~ (l1_pre_topc @ X4)
% 5.44/5.61          | (v2_struct_0 @ X6)
% 5.44/5.61          | ~ (m1_pre_topc @ X6 @ X4)
% 5.44/5.61          | ((u1_struct_0 @ (k1_tsep_1 @ X4 @ X3 @ X6))
% 5.44/5.61              = (k2_xboole_0 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X6)))
% 5.44/5.61          | ~ (m1_pre_topc @ (k1_tsep_1 @ X4 @ X3 @ X6) @ X4)
% 5.44/5.61          | ~ (v1_pre_topc @ (k1_tsep_1 @ X4 @ X3 @ X6))
% 5.44/5.61          | (v2_struct_0 @ (k1_tsep_1 @ X4 @ X3 @ X6))
% 5.44/5.61          | ~ (m1_pre_topc @ X3 @ X4)
% 5.44/5.61          | (v2_struct_0 @ X3))),
% 5.44/5.61      inference('simplify', [status(thm)], ['39'])).
% 5.44/5.61  thf('41', plain,
% 5.44/5.61      (((v2_struct_0 @ sk_D)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 5.44/5.61        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_D)
% 5.44/5.61        | ~ (l1_pre_topc @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_A))),
% 5.44/5.61      inference('sup-', [status(thm)], ['38', '40'])).
% 5.44/5.61  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('43', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.61  thf('45', plain,
% 5.44/5.61      (((v2_struct_0 @ sk_D)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 5.44/5.61        | (v2_struct_0 @ sk_D)
% 5.44/5.61        | (v2_struct_0 @ sk_A))),
% 5.44/5.61      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 5.44/5.61  thf('46', plain,
% 5.44/5.61      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 5.44/5.61        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_D))),
% 5.44/5.61      inference('simplify', [status(thm)], ['45'])).
% 5.44/5.61  thf('47', plain,
% 5.44/5.61      (((v2_struct_0 @ sk_D)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_D)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))),
% 5.44/5.61      inference('sup-', [status(thm)], ['37', '46'])).
% 5.44/5.61  thf('48', plain,
% 5.44/5.61      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 5.44/5.61        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_D))),
% 5.44/5.61      inference('simplify', [status(thm)], ['47'])).
% 5.44/5.61  thf('49', plain,
% 5.44/5.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.44/5.61         (~ (m1_pre_topc @ X7 @ X8)
% 5.44/5.61          | (v2_struct_0 @ X7)
% 5.44/5.61          | ~ (l1_pre_topc @ X8)
% 5.44/5.61          | (v2_struct_0 @ X8)
% 5.44/5.61          | (v2_struct_0 @ X9)
% 5.44/5.61          | ~ (m1_pre_topc @ X9 @ X8)
% 5.44/5.61          | ~ (v2_struct_0 @ (k1_tsep_1 @ X8 @ X7 @ X9)))),
% 5.44/5.61      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 5.44/5.61  thf('50', plain,
% 5.44/5.61      (((v2_struct_0 @ sk_D)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.61            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 5.44/5.61        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_D)
% 5.44/5.61        | (v2_struct_0 @ sk_A)
% 5.44/5.61        | ~ (l1_pre_topc @ sk_A)
% 5.44/5.61        | (v2_struct_0 @ sk_B)
% 5.44/5.61        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 5.44/5.61      inference('sup-', [status(thm)], ['48', '49'])).
% 5.44/5.62  thf('51', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('53', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('54', plain,
% 5.44/5.62      (((v2_struct_0 @ sk_D)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_B)
% 5.44/5.62        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.62            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 5.44/5.62        | (v2_struct_0 @ sk_D)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_B))),
% 5.44/5.62      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 5.44/5.62  thf('55', plain,
% 5.44/5.62      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D))
% 5.44/5.62          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 5.44/5.62        | (v2_struct_0 @ sk_B)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_D))),
% 5.44/5.62      inference('simplify', [status(thm)], ['54'])).
% 5.44/5.62  thf('56', plain,
% 5.44/5.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.44/5.62         (~ (m1_pre_topc @ X10 @ X11)
% 5.44/5.62          | ~ (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 5.44/5.62          | (m1_pre_topc @ X10 @ X12)
% 5.44/5.62          | ~ (m1_pre_topc @ X12 @ X11)
% 5.44/5.62          | ~ (l1_pre_topc @ X11)
% 5.44/5.62          | ~ (v2_pre_topc @ X11))),
% 5.44/5.62      inference('cnf', [status(esa)], [t4_tsep_1])).
% 5.44/5.62  thf('57', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]:
% 5.44/5.62         (~ (r1_tarski @ 
% 5.44/5.62             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)) @ 
% 5.44/5.62             (u1_struct_0 @ X0))
% 5.44/5.62          | (v2_struct_0 @ sk_D)
% 5.44/5.62          | (v2_struct_0 @ sk_A)
% 5.44/5.62          | (v2_struct_0 @ sk_B)
% 5.44/5.62          | ~ (v2_pre_topc @ X1)
% 5.44/5.62          | ~ (l1_pre_topc @ X1)
% 5.44/5.62          | ~ (m1_pre_topc @ X0 @ X1)
% 5.44/5.62          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 5.44/5.62          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X1))),
% 5.44/5.62      inference('sup-', [status(thm)], ['55', '56'])).
% 5.44/5.62  thf('58', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ X0)
% 5.44/5.62          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 5.44/5.62          | ~ (m1_pre_topc @ sk_C @ X0)
% 5.44/5.62          | ~ (l1_pre_topc @ X0)
% 5.44/5.62          | ~ (v2_pre_topc @ X0)
% 5.44/5.62          | (v2_struct_0 @ sk_B)
% 5.44/5.62          | (v2_struct_0 @ sk_A)
% 5.44/5.62          | (v2_struct_0 @ sk_D))),
% 5.44/5.62      inference('sup-', [status(thm)], ['30', '57'])).
% 5.44/5.62  thf('59', plain,
% 5.44/5.62      (((v2_struct_0 @ sk_D)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_B)
% 5.44/5.62        | (v2_struct_0 @ sk_D)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_B)
% 5.44/5.62        | ~ (v2_pre_topc @ sk_A)
% 5.44/5.62        | ~ (l1_pre_topc @ sk_A)
% 5.44/5.62        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 5.44/5.62        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C))),
% 5.44/5.62      inference('sup-', [status(thm)], ['7', '58'])).
% 5.44/5.62  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('62', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('63', plain,
% 5.44/5.62      (((v2_struct_0 @ sk_D)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_B)
% 5.44/5.62        | (v2_struct_0 @ sk_D)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_B)
% 5.44/5.62        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C))),
% 5.44/5.62      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 5.44/5.62  thf('64', plain,
% 5.44/5.62      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)
% 5.44/5.62        | (v2_struct_0 @ sk_B)
% 5.44/5.62        | (v2_struct_0 @ sk_A)
% 5.44/5.62        | (v2_struct_0 @ sk_D))),
% 5.44/5.62      inference('simplify', [status(thm)], ['63'])).
% 5.44/5.62  thf('65', plain, (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('66', plain,
% 5.44/5.62      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 5.44/5.62      inference('sup-', [status(thm)], ['64', '65'])).
% 5.44/5.62  thf('67', plain, (~ (v2_struct_0 @ sk_D)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('68', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 5.44/5.62      inference('clc', [status(thm)], ['66', '67'])).
% 5.44/5.62  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('70', plain, ((v2_struct_0 @ sk_A)),
% 5.44/5.62      inference('clc', [status(thm)], ['68', '69'])).
% 5.44/5.62  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 5.44/5.62  
% 5.44/5.62  % SZS output end Refutation
% 5.44/5.62  
% 5.44/5.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
