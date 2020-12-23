%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yJqNFMSvQA

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 107 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  662 (2102 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( m1_pre_topc @ X6 @ X8 )
      | ( r1_tsep_1 @ X6 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X7 @ X6 @ X9 ) @ ( k2_tsep_1 @ X7 @ X8 @ X10 ) )
      | ~ ( m1_pre_topc @ X10 @ X7 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k2_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( ( k2_tsep_1 @ X5 @ X4 @ X4 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t26_tmap_1])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tsep_1 @ sk_A @ sk_D @ sk_D )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_D ) @ ( u1_pre_topc @ sk_D ) ) ),
    inference(clc,[status(thm)],['25','26'])).

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
      ( ~ ( m1_pre_topc @ X0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) )
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
      ( ~ ( m1_pre_topc @ X0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_D ) )
      | ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yJqNFMSvQA
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:48:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 50 iterations in 0.041s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(t30_tmap_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.50                   ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.50                     ( ( r1_tsep_1 @ B @ C ) | 
% 0.21/0.50                       ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.50                      ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.50                        ( ( r1_tsep_1 @ B @ C ) | 
% 0.21/0.50                          ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t30_tmap_1])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t28_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.50                   ( ![E:$i]:
% 0.21/0.50                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.21/0.50                       ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 0.21/0.50                         ( ( r1_tsep_1 @ B @ C ) | 
% 0.21/0.50                           ( m1_pre_topc @
% 0.21/0.50                             ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.21/0.50                             ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X6)
% 0.21/0.50          | ~ (m1_pre_topc @ X6 @ X7)
% 0.21/0.50          | (v2_struct_0 @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X8 @ X7)
% 0.21/0.50          | ~ (m1_pre_topc @ X6 @ X8)
% 0.21/0.50          | (r1_tsep_1 @ X6 @ X9)
% 0.21/0.50          | ~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.50          | (m1_pre_topc @ (k2_tsep_1 @ X7 @ X6 @ X9) @ 
% 0.21/0.50             (k2_tsep_1 @ X7 @ X8 @ X10))
% 0.21/0.50          | ~ (m1_pre_topc @ X10 @ X7)
% 0.21/0.50          | (v2_struct_0 @ X10)
% 0.21/0.50          | ~ (m1_pre_topc @ X9 @ X7)
% 0.21/0.50          | (v2_struct_0 @ X9)
% 0.21/0.50          | ~ (l1_pre_topc @ X7)
% 0.21/0.50          | ~ (v2_pre_topc @ X7)
% 0.21/0.50          | (v2_struct_0 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t28_tmap_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.21/0.50          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.50             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.50          | (r1_tsep_1 @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.21/0.50          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X2)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.21/0.50          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.21/0.50             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.50          | (r1_tsep_1 @ sk_B @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.21/0.50          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X2)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.50          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.21/0.50          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 0.21/0.50          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_C)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_C)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.50          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50             (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50          | ~ (m1_pre_topc @ sk_B @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '10'])).
% 0.21/0.50  thf('12', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_C)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.50          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50             (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.21/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50          | (v2_struct_0 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.50        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50           (k2_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '13'])).
% 0.21/0.50  thf('15', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50           (k2_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50           (k2_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.21/0.50        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.50  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t26_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50           ( ( k2_tsep_1 @ A @ B @ B ) =
% 0.21/0.50             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X4)
% 0.21/0.50          | ~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.50          | ((k2_tsep_1 @ X5 @ X4 @ X4)
% 0.21/0.50              = (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.21/0.50          | ~ (l1_pre_topc @ X5)
% 0.21/0.50          | ~ (v2_pre_topc @ X5)
% 0.21/0.50          | (v2_struct_0 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t26_tmap_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | ((k2_tsep_1 @ sk_A @ sk_D @ sk_D)
% 0.21/0.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 0.21/0.50        | (v2_struct_0 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ((k2_tsep_1 @ sk_A @ sk_D @ sk_D)
% 0.21/0.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))
% 0.21/0.50        | (v2_struct_0 @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.50  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_D)
% 0.21/0.50        | ((k2_tsep_1 @ sk_A @ sk_D @ sk_D)
% 0.21/0.50            = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D))))),
% 0.21/0.50      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((k2_tsep_1 @ sk_A @ sk_D @ sk_D)
% 0.21/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_D) @ (u1_pre_topc @ sk_D)))),
% 0.21/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf(t59_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_pre_topc @
% 0.21/0.50             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.50           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X2 @ 
% 0.21/0.50             (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.21/0.50          | (m1_pre_topc @ X2 @ X3)
% 0.21/0.50          | ~ (l1_pre_topc @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.50          | (m1_pre_topc @ X0 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_m1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.50  thf('32', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_D))
% 0.21/0.50          | (m1_pre_topc @ X0 @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '35'])).
% 0.21/0.50  thf('37', plain, (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_D)
% 0.21/0.50        | (v2_struct_0 @ sk_C)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.21/0.50      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.50  thf('45', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('46', plain, ((v2_struct_0 @ sk_D)),
% 0.21/0.50      inference('clc', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
