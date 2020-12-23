%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mvvgAmZE5W

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:32 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 256 expanded)
%              Number of leaves         :   16 (  73 expanded)
%              Depth                    :   25
%              Number of atoms          : 1082 (6893 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

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

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X10 ) )
      | ( m1_pre_topc @ X8 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_pre_topc @ sk_B @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( m1_pre_topc @ X3 @ X5 )
      | ( r1_tsep_1 @ X3 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X4 @ X3 @ X6 ) @ ( k2_tsep_1 @ X4 @ X5 @ X7 ) )
      | ~ ( m1_pre_topc @ X7 @ X4 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X6 @ X4 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_tmap_1])).

thf('18',plain,(
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
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
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
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) )
    | ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( m1_pre_topc @ sk_C @ sk_D )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
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
    inference('sup-',[status(thm)],['15','21'])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
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
    inference(demod,[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['29'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
      & ( m1_pre_topc @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['31','33','60'])).

thf('62',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['30','61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['28','62'])).

thf('64',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ~ ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_D ) )
    | ( m1_pre_topc @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['12'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','73','74','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mvvgAmZE5W
% 0.14/0.37  % Computer   : n012.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:19:52 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 90 iterations in 0.065s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.56  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.24/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.56  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.24/0.56  thf(t32_tmap_1, conjecture,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.24/0.56           ( ![C:$i]:
% 0.24/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.56               ( ![D:$i]:
% 0.24/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.56                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.24/0.56                     ( ( ( m1_pre_topc @ B @ D ) =>
% 0.24/0.56                         ( m1_pre_topc @
% 0.24/0.56                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.24/0.56                           ( k2_tsep_1 @ A @ D @ C ) ) ) & 
% 0.24/0.56                       ( ( m1_pre_topc @ C @ D ) =>
% 0.24/0.56                         ( m1_pre_topc @
% 0.24/0.56                           ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.24/0.56                           ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i]:
% 0.24/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.56            ( l1_pre_topc @ A ) ) =>
% 0.24/0.56          ( ![B:$i]:
% 0.24/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.24/0.56              ( ![C:$i]:
% 0.24/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.56                  ( ![D:$i]:
% 0.24/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.56                      ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.24/0.56                        ( ( ( m1_pre_topc @ B @ D ) =>
% 0.24/0.56                            ( m1_pre_topc @
% 0.24/0.56                              ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.24/0.56                              ( k2_tsep_1 @ A @ D @ C ) ) ) & 
% 0.24/0.56                          ( ( m1_pre_topc @ C @ D ) =>
% 0.24/0.56                            ( m1_pre_topc @
% 0.24/0.56                              ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.24/0.56                              ( k2_tsep_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t32_tmap_1])).
% 0.24/0.56  thf('0', plain,
% 0.24/0.56      (((m1_pre_topc @ sk_B @ sk_D) | (m1_pre_topc @ sk_C @ sk_D))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('1', plain,
% 0.24/0.56      (((m1_pre_topc @ sk_C @ sk_D)) | ((m1_pre_topc @ sk_B @ sk_D))),
% 0.24/0.56      inference('split', [status(esa)], ['0'])).
% 0.24/0.56  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(d10_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.56  thf('3', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.56  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.24/0.56  thf(t4_tsep_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.56           ( ![C:$i]:
% 0.24/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.24/0.56               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.24/0.56                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.24/0.56  thf('5', plain,
% 0.24/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.56         (~ (m1_pre_topc @ X8 @ X9)
% 0.24/0.56          | ~ (r1_tarski @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X10))
% 0.24/0.56          | (m1_pre_topc @ X8 @ X10)
% 0.24/0.56          | ~ (m1_pre_topc @ X10 @ X9)
% 0.24/0.56          | ~ (l1_pre_topc @ X9)
% 0.24/0.56          | ~ (v2_pre_topc @ X9))),
% 0.24/0.56      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.24/0.56  thf('6', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (v2_pre_topc @ X1)
% 0.24/0.56          | ~ (l1_pre_topc @ X1)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.56          | (m1_pre_topc @ X0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.24/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.56  thf('7', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((m1_pre_topc @ X0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.56          | ~ (l1_pre_topc @ X1)
% 0.24/0.56          | ~ (v2_pre_topc @ X1))),
% 0.24/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.56  thf('8', plain,
% 0.24/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.56        | (m1_pre_topc @ sk_C @ sk_C))),
% 0.24/0.56      inference('sup-', [status(thm)], ['2', '7'])).
% 0.24/0.56  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.24/0.56  thf('12', plain,
% 0.24/0.56      (((m1_pre_topc @ sk_B @ sk_D)
% 0.24/0.56        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('13', plain,
% 0.24/0.56      (((m1_pre_topc @ sk_B @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('split', [status(esa)], ['12'])).
% 0.24/0.56  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('15', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(t28_tmap_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.24/0.56           ( ![C:$i]:
% 0.24/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.56               ( ![D:$i]:
% 0.24/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.56                   ( ![E:$i]:
% 0.24/0.56                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.24/0.56                       ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 0.24/0.56                         ( ( r1_tsep_1 @ B @ C ) | 
% 0.24/0.56                           ( m1_pre_topc @
% 0.24/0.56                             ( k2_tsep_1 @ A @ B @ C ) @ 
% 0.24/0.56                             ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.56         ((v2_struct_0 @ X3)
% 0.24/0.56          | ~ (m1_pre_topc @ X3 @ X4)
% 0.24/0.56          | (v2_struct_0 @ X5)
% 0.24/0.56          | ~ (m1_pre_topc @ X5 @ X4)
% 0.24/0.56          | ~ (m1_pre_topc @ X3 @ X5)
% 0.24/0.56          | (r1_tsep_1 @ X3 @ X6)
% 0.24/0.56          | ~ (m1_pre_topc @ X6 @ X7)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ X4 @ X3 @ X6) @ 
% 0.24/0.56             (k2_tsep_1 @ X4 @ X5 @ X7))
% 0.24/0.56          | ~ (m1_pre_topc @ X7 @ X4)
% 0.24/0.56          | (v2_struct_0 @ X7)
% 0.24/0.56          | ~ (m1_pre_topc @ X6 @ X4)
% 0.24/0.56          | (v2_struct_0 @ X6)
% 0.24/0.56          | ~ (l1_pre_topc @ X4)
% 0.24/0.56          | ~ (v2_pre_topc @ X4)
% 0.24/0.56          | (v2_struct_0 @ X4))),
% 0.24/0.56      inference('cnf', [status(esa)], [t28_tmap_1])).
% 0.24/0.56  thf('18', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_A)
% 0.24/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X1)
% 0.24/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.24/0.56          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X2)
% 0.24/0.56          | (v2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.56  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X1)
% 0.24/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ X2 @ X1))
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_B @ X2)
% 0.24/0.56          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X2)
% 0.24/0.56          | (v2_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.24/0.56  thf('22', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_B)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 0.24/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X1)
% 0.24/0.56          | (v2_struct_0 @ sk_C)
% 0.24/0.56          | (v2_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup-', [status(thm)], ['15', '21'])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ sk_C)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.24/0.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_B @ sk_D)
% 0.24/0.56          | (v2_struct_0 @ sk_D)
% 0.24/0.56          | (v2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['14', '22'])).
% 0.24/0.56  thf('24', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          ((v2_struct_0 @ sk_B)
% 0.24/0.56           | (v2_struct_0 @ sk_D)
% 0.24/0.56           | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.24/0.56           | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56              (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 0.24/0.56           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56           | (v2_struct_0 @ X0)
% 0.24/0.56           | (v2_struct_0 @ sk_C)
% 0.24/0.56           | (v2_struct_0 @ sk_A)))
% 0.24/0.56         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['13', '23'])).
% 0.24/0.56  thf('25', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_A)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.24/0.56         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.24/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['11', '24'])).
% 0.24/0.56  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_A)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.24/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.24/0.56  thf('28', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_B)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56            (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56           (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.24/0.56        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('30', plain,
% 0.24/0.56      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56           (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))
% 0.24/0.56         <= (~
% 0.24/0.56             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56               (k2_tsep_1 @ sk_A @ sk_D @ sk_C))))),
% 0.24/0.56      inference('split', [status(esa)], ['29'])).
% 0.24/0.56  thf('31', plain,
% 0.24/0.56      (~
% 0.24/0.56       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56         (k2_tsep_1 @ sk_A @ sk_D @ sk_C))) | 
% 0.24/0.56       ~
% 0.24/0.56       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56         (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))),
% 0.24/0.56      inference('split', [status(esa)], ['29'])).
% 0.24/0.56  thf('32', plain,
% 0.24/0.56      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56           (k2_tsep_1 @ sk_A @ sk_D @ sk_C))
% 0.24/0.56        | (m1_pre_topc @ sk_C @ sk_D))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('33', plain,
% 0.24/0.56      (((m1_pre_topc @ sk_C @ sk_D)) | 
% 0.24/0.56       ~
% 0.24/0.56       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56         (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))),
% 0.24/0.56      inference('split', [status(esa)], ['32'])).
% 0.24/0.56  thf('34', plain,
% 0.24/0.56      (((m1_pre_topc @ sk_C @ sk_D)) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('split', [status(esa)], ['32'])).
% 0.24/0.56  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('36', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_B)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ X0 @ X1))
% 0.24/0.56          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X1)
% 0.24/0.56          | (v2_struct_0 @ sk_C)
% 0.24/0.56          | (v2_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup-', [status(thm)], ['15', '21'])).
% 0.24/0.56  thf('37', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ sk_C)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.24/0.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.24/0.56          | (v2_struct_0 @ sk_B)
% 0.24/0.56          | (v2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.24/0.56  thf('38', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('39', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         ((m1_pre_topc @ X0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.56          | ~ (l1_pre_topc @ X1)
% 0.24/0.56          | ~ (v2_pre_topc @ X1))),
% 0.24/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.56  thf('40', plain,
% 0.24/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.56        | (m1_pre_topc @ sk_B @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.24/0.56  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.24/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.24/0.56  thf('44', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ sk_C)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.24/0.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56          | (v2_struct_0 @ sk_B)
% 0.24/0.56          | (v2_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['37', '43'])).
% 0.24/0.56  thf('45', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((v2_struct_0 @ sk_B)
% 0.24/0.56          | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.24/0.56          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56             (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.24/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.56          | (v2_struct_0 @ X0)
% 0.24/0.56          | (v2_struct_0 @ sk_C)
% 0.24/0.56          | (v2_struct_0 @ sk_A))),
% 0.24/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.24/0.56  thf('46', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_A)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.24/0.56         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56            (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.24/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['34', '45'])).
% 0.24/0.56  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('48', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_A)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56            (k2_tsep_1 @ sk_A @ sk_B @ sk_D))
% 0.24/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.24/0.56  thf('49', plain,
% 0.24/0.56      ((~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56           (k2_tsep_1 @ sk_A @ sk_B @ sk_D)))
% 0.24/0.56         <= (~
% 0.24/0.56             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))))),
% 0.24/0.56      inference('split', [status(esa)], ['29'])).
% 0.24/0.56  thf('50', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_B)
% 0.24/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_A)))
% 0.24/0.56         <= (~
% 0.24/0.56             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.24/0.56             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.24/0.56  thf('51', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('52', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_A)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (v2_struct_0 @ sk_B)))
% 0.24/0.56         <= (~
% 0.24/0.56             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.24/0.56             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.24/0.56  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('54', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.24/0.56         <= (~
% 0.24/0.56             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.24/0.56             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.24/0.56  thf('55', plain, (~ (v2_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('56', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.24/0.56         <= (~
% 0.24/0.56             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.24/0.56             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('clc', [status(thm)], ['54', '55'])).
% 0.24/0.56  thf('57', plain, (~ (v2_struct_0 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('58', plain,
% 0.24/0.56      (((v2_struct_0 @ sk_D))
% 0.24/0.56         <= (~
% 0.24/0.56             ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56               (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) & 
% 0.24/0.56             ((m1_pre_topc @ sk_C @ sk_D)))),
% 0.24/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.24/0.56  thf('59', plain, (~ (v2_struct_0 @ sk_D)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('60', plain,
% 0.24/0.56      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56         (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.24/0.56       ~ ((m1_pre_topc @ sk_C @ sk_D))),
% 0.24/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.24/0.56  thf('61', plain,
% 0.24/0.56      (~
% 0.24/0.56       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56         (k2_tsep_1 @ sk_A @ sk_D @ sk_C)))),
% 0.24/0.56      inference('sat_resolution*', [status(thm)], ['31', '33', '60'])).
% 0.24/0.56  thf('62', plain,
% 0.24/0.56      (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56          (k2_tsep_1 @ sk_A @ sk_D @ sk_C))),
% 0.24/0.56      inference('simpl_trail', [status(thm)], ['30', '61'])).
% 0.24/0.56  thf('63', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_A)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (v2_struct_0 @ sk_B))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['28', '62'])).
% 0.24/0.56  thf('64', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('65', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_B)
% 0.24/0.56         | (v2_struct_0 @ sk_D)
% 0.24/0.56         | (v2_struct_0 @ sk_C)
% 0.24/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.24/0.56  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('67', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.24/0.56         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.24/0.56  thf('68', plain, (~ (v2_struct_0 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('69', plain,
% 0.24/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.24/0.56         <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('clc', [status(thm)], ['67', '68'])).
% 0.24/0.56  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('71', plain, (((v2_struct_0 @ sk_D)) <= (((m1_pre_topc @ sk_B @ sk_D)))),
% 0.24/0.56      inference('clc', [status(thm)], ['69', '70'])).
% 0.24/0.56  thf('72', plain, (~ (v2_struct_0 @ sk_D)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('73', plain, (~ ((m1_pre_topc @ sk_B @ sk_D))),
% 0.24/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.24/0.56  thf('74', plain,
% 0.24/0.56      (~
% 0.24/0.56       ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.24/0.56         (k2_tsep_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.24/0.56       ((m1_pre_topc @ sk_B @ sk_D))),
% 0.24/0.56      inference('split', [status(esa)], ['12'])).
% 0.24/0.56  thf('75', plain, ($false),
% 0.24/0.56      inference('sat_resolution*', [status(thm)], ['1', '73', '74', '60'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.24/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
