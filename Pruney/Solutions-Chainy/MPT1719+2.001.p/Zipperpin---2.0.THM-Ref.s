%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OYqObFOA5U

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:27 EST 2020

% Result     : Theorem 53.94s
% Output     : Refutation 53.94s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 327 expanded)
%              Number of leaves         :   28 ( 102 expanded)
%              Depth                    :   32
%              Number of atoms          : 2321 (8179 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t28_tmap_1,conjecture,(
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
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( m1_pre_topc @ B @ D )
                            & ( m1_pre_topc @ C @ E ) )
                         => ( ( r1_tsep_1 @ B @ C )
                            | ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( m1_pre_topc @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( m1_pre_topc @ C @ A )
                & ~ ( v2_struct_0 @ C ) )
             => ! [D: $i] :
                  ( ( ( m1_pre_topc @ D @ A )
                    & ~ ( v2_struct_0 @ D ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ B @ D ) )
                      | ( ~ ( r1_tsep_1 @ D @ C )
                        & ~ ( r1_tsep_1 @ C @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i] :
      ( ( zip_tseitin_1 @ D @ C )
     => ( ~ ( r1_tsep_1 @ C @ D )
        & ~ ( r1_tsep_1 @ D @ C ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ B )
     => ( ( r1_tsep_1 @ B @ D )
        & ( r1_tsep_1 @ D @ B ) ) ) )).

thf(zf_stmt_5,axiom,(
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
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( zip_tseitin_1 @ D @ C )
                      | ( zip_tseitin_0 @ D @ B ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( zip_tseitin_0 @ X17 @ X15 )
      | ( zip_tseitin_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_C @ sk_E )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ sk_E )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( zip_tseitin_1 @ sk_B @ sk_E )
    | ( zip_tseitin_0 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( zip_tseitin_1 @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( zip_tseitin_0 @ X17 @ X15 )
      | ( zip_tseitin_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_B @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D )
    | ( zip_tseitin_0 @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tsep_1 @ X11 @ X12 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( zip_tseitin_1 @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X14 @ X13 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( zip_tseitin_1 @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

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

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( r1_tsep_1 @ X4 @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X5 )
      | ( X7
       != ( k2_tsep_1 @ X5 @ X4 @ X6 ) )
      | ( ( u1_struct_0 @ X7 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) @ X5 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) )
      | ( r1_tsep_1 @ X4 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('82',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) @ X5 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X5 @ X4 @ X6 ) )
      | ( r1_tsep_1 @ X4 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('83',plain,
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
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
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
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
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
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('92',plain,
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
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

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

thf('98',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) )
      | ( m1_pre_topc @ X19 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('99',plain,(
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
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_E )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_C @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(t27_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t27_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X1 ) @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['110','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( r1_tsep_1 @ sk_D @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','130'])).

thf('132',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_E )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tsep_1 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ~ ( zip_tseitin_1 @ sk_E @ sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_struct_0 @ sk_E ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['0','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OYqObFOA5U
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:10:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 53.94/54.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 53.94/54.17  % Solved by: fo/fo7.sh
% 53.94/54.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 53.94/54.17  % done 5517 iterations in 53.711s
% 53.94/54.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 53.94/54.17  % SZS output start Refutation
% 53.94/54.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 53.94/54.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 53.94/54.17  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 53.94/54.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 53.94/54.17  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 53.94/54.17  thf(sk_B_type, type, sk_B: $i).
% 53.94/54.17  thf(sk_C_type, type, sk_C: $i).
% 53.94/54.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 53.94/54.17  thf(sk_E_type, type, sk_E: $i).
% 53.94/54.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 53.94/54.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 53.94/54.17  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 53.94/54.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 53.94/54.17  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 53.94/54.17  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 53.94/54.17  thf(sk_D_type, type, sk_D: $i).
% 53.94/54.17  thf(sk_A_type, type, sk_A: $i).
% 53.94/54.17  thf(t28_tmap_1, conjecture,
% 53.94/54.17    (![A:$i]:
% 53.94/54.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 53.94/54.17       ( ![B:$i]:
% 53.94/54.17         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 53.94/54.17           ( ![C:$i]:
% 53.94/54.17             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.94/54.17               ( ![D:$i]:
% 53.94/54.17                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 53.94/54.17                   ( ![E:$i]:
% 53.94/54.17                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 53.94/54.17                       ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 53.94/54.17                         ( ( r1_tsep_1 @ B @ C ) | 
% 53.94/54.17                           ( m1_pre_topc @
% 53.94/54.17                             ( k2_tsep_1 @ A @ B @ C ) @ 
% 53.94/54.17                             ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 53.94/54.17  thf(zf_stmt_0, negated_conjecture,
% 53.94/54.17    (~( ![A:$i]:
% 53.94/54.17        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 53.94/54.17            ( l1_pre_topc @ A ) ) =>
% 53.94/54.17          ( ![B:$i]:
% 53.94/54.17            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 53.94/54.17              ( ![C:$i]:
% 53.94/54.17                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.94/54.17                  ( ![D:$i]:
% 53.94/54.17                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 53.94/54.17                      ( ![E:$i]:
% 53.94/54.17                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 53.94/54.17                          ( ( ( m1_pre_topc @ B @ D ) & ( m1_pre_topc @ C @ E ) ) =>
% 53.94/54.17                            ( ( r1_tsep_1 @ B @ C ) | 
% 53.94/54.17                              ( m1_pre_topc @
% 53.94/54.17                                ( k2_tsep_1 @ A @ B @ C ) @ 
% 53.94/54.17                                ( k2_tsep_1 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 53.94/54.17    inference('cnf.neg', [status(esa)], [t28_tmap_1])).
% 53.94/54.17  thf('0', plain, (~ (v2_struct_0 @ sk_E)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('2', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf(t24_tmap_1, axiom,
% 53.94/54.17    (![A:$i]:
% 53.94/54.17     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 53.94/54.17       ( ![B:$i]:
% 53.94/54.17         ( ( ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 53.94/54.17           ( ![C:$i]:
% 53.94/54.17             ( ( ( m1_pre_topc @ C @ A ) & ( ~( v2_struct_0 @ C ) ) ) =>
% 53.94/54.17               ( ![D:$i]:
% 53.94/54.17                 ( ( ( m1_pre_topc @ D @ A ) & ( ~( v2_struct_0 @ D ) ) ) =>
% 53.94/54.17                   ( ( m1_pre_topc @ B @ C ) =>
% 53.94/54.17                     ( ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ B @ D ) ) | 
% 53.94/54.17                       ( ( ~( r1_tsep_1 @ D @ C ) ) & 
% 53.94/54.17                         ( ~( r1_tsep_1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 53.94/54.17  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 53.94/54.17  thf(zf_stmt_2, axiom,
% 53.94/54.17    (![D:$i,C:$i]:
% 53.94/54.17     ( ( zip_tseitin_1 @ D @ C ) =>
% 53.94/54.17       ( ( ~( r1_tsep_1 @ C @ D ) ) & ( ~( r1_tsep_1 @ D @ C ) ) ) ))).
% 53.94/54.17  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 53.94/54.17  thf(zf_stmt_4, axiom,
% 53.94/54.17    (![D:$i,B:$i]:
% 53.94/54.17     ( ( zip_tseitin_0 @ D @ B ) =>
% 53.94/54.17       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ))).
% 53.94/54.17  thf(zf_stmt_5, axiom,
% 53.94/54.17    (![A:$i]:
% 53.94/54.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 53.94/54.17       ( ![B:$i]:
% 53.94/54.17         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 53.94/54.17           ( ![C:$i]:
% 53.94/54.17             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.94/54.17               ( ![D:$i]:
% 53.94/54.17                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 53.94/54.17                   ( ( m1_pre_topc @ B @ C ) =>
% 53.94/54.17                     ( ( zip_tseitin_1 @ D @ C ) | ( zip_tseitin_0 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 53.94/54.17  thf('4', plain,
% 53.94/54.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 53.94/54.17         ((v2_struct_0 @ X15)
% 53.94/54.17          | ~ (m1_pre_topc @ X15 @ X16)
% 53.94/54.17          | (v2_struct_0 @ X17)
% 53.94/54.17          | ~ (m1_pre_topc @ X17 @ X16)
% 53.94/54.17          | (zip_tseitin_0 @ X17 @ X15)
% 53.94/54.17          | (zip_tseitin_1 @ X17 @ X18)
% 53.94/54.17          | ~ (m1_pre_topc @ X15 @ X18)
% 53.94/54.17          | ~ (m1_pre_topc @ X18 @ X16)
% 53.94/54.17          | (v2_struct_0 @ X18)
% 53.94/54.17          | ~ (l1_pre_topc @ X16)
% 53.94/54.17          | ~ (v2_pre_topc @ X16)
% 53.94/54.17          | (v2_struct_0 @ X16))),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 53.94/54.17  thf('5', plain,
% 53.94/54.17      (![X0 : $i, X1 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_A)
% 53.94/54.17          | ~ (v2_pre_topc @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ sk_C @ X0)
% 53.94/54.17          | (zip_tseitin_1 @ X1 @ X0)
% 53.94/54.17          | (zip_tseitin_0 @ X1 @ sk_C)
% 53.94/54.17          | ~ (m1_pre_topc @ X1 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X1)
% 53.94/54.17          | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['3', '4'])).
% 53.94/54.17  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('8', plain,
% 53.94/54.17      (![X0 : $i, X1 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ sk_C @ X0)
% 53.94/54.17          | (zip_tseitin_1 @ X1 @ X0)
% 53.94/54.17          | (zip_tseitin_0 @ X1 @ sk_C)
% 53.94/54.17          | ~ (m1_pre_topc @ X1 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X1)
% 53.94/54.17          | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('demod', [status(thm)], ['5', '6', '7'])).
% 53.94/54.17  thf('9', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_C)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (zip_tseitin_0 @ X0 @ sk_C)
% 53.94/54.17          | (zip_tseitin_1 @ X0 @ sk_E)
% 53.94/54.17          | ~ (m1_pre_topc @ sk_C @ sk_E)
% 53.94/54.17          | (v2_struct_0 @ sk_E)
% 53.94/54.17          | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['2', '8'])).
% 53.94/54.17  thf('10', plain, ((m1_pre_topc @ sk_C @ sk_E)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('11', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_C)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (zip_tseitin_0 @ X0 @ sk_C)
% 53.94/54.17          | (zip_tseitin_1 @ X0 @ sk_E)
% 53.94/54.17          | (v2_struct_0 @ sk_E)
% 53.94/54.17          | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('demod', [status(thm)], ['9', '10'])).
% 53.94/54.17  thf('12', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (zip_tseitin_1 @ sk_B @ sk_E)
% 53.94/54.17        | (zip_tseitin_0 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['1', '11'])).
% 53.94/54.17  thf('13', plain,
% 53.94/54.17      (![X11 : $i, X12 : $i]:
% 53.94/54.17         ((r1_tsep_1 @ X12 @ X11) | ~ (zip_tseitin_0 @ X12 @ X11))),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 53.94/54.17  thf('14', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (zip_tseitin_1 @ sk_B @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['12', '13'])).
% 53.94/54.17  thf('15', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('16', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (zip_tseitin_1 @ sk_B @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['14', '15'])).
% 53.94/54.17  thf('17', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('20', plain,
% 53.94/54.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 53.94/54.17         ((v2_struct_0 @ X15)
% 53.94/54.17          | ~ (m1_pre_topc @ X15 @ X16)
% 53.94/54.17          | (v2_struct_0 @ X17)
% 53.94/54.17          | ~ (m1_pre_topc @ X17 @ X16)
% 53.94/54.17          | (zip_tseitin_0 @ X17 @ X15)
% 53.94/54.17          | (zip_tseitin_1 @ X17 @ X18)
% 53.94/54.17          | ~ (m1_pre_topc @ X15 @ X18)
% 53.94/54.17          | ~ (m1_pre_topc @ X18 @ X16)
% 53.94/54.17          | (v2_struct_0 @ X18)
% 53.94/54.17          | ~ (l1_pre_topc @ X16)
% 53.94/54.17          | ~ (v2_pre_topc @ X16)
% 53.94/54.17          | (v2_struct_0 @ X16))),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 53.94/54.17  thf('21', plain,
% 53.94/54.17      (![X0 : $i, X1 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_A)
% 53.94/54.17          | ~ (v2_pre_topc @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ sk_B @ X0)
% 53.94/54.17          | (zip_tseitin_1 @ X1 @ X0)
% 53.94/54.17          | (zip_tseitin_0 @ X1 @ sk_B)
% 53.94/54.17          | ~ (m1_pre_topc @ X1 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X1)
% 53.94/54.17          | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('sup-', [status(thm)], ['19', '20'])).
% 53.94/54.17  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('24', plain,
% 53.94/54.17      (![X0 : $i, X1 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ sk_B @ X0)
% 53.94/54.17          | (zip_tseitin_1 @ X1 @ X0)
% 53.94/54.17          | (zip_tseitin_0 @ X1 @ sk_B)
% 53.94/54.17          | ~ (m1_pre_topc @ X1 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X1)
% 53.94/54.17          | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('demod', [status(thm)], ['21', '22', '23'])).
% 53.94/54.17  thf('25', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_B)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (zip_tseitin_0 @ X0 @ sk_B)
% 53.94/54.17          | (zip_tseitin_1 @ X0 @ sk_D)
% 53.94/54.17          | ~ (m1_pre_topc @ sk_B @ sk_D)
% 53.94/54.17          | (v2_struct_0 @ sk_D)
% 53.94/54.17          | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['18', '24'])).
% 53.94/54.17  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('27', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_B)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (zip_tseitin_0 @ X0 @ sk_B)
% 53.94/54.17          | (zip_tseitin_1 @ X0 @ sk_D)
% 53.94/54.17          | (v2_struct_0 @ sk_D)
% 53.94/54.17          | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('demod', [status(thm)], ['25', '26'])).
% 53.94/54.17  thf('28', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (zip_tseitin_1 @ sk_E @ sk_D)
% 53.94/54.17        | (zip_tseitin_0 @ sk_E @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('sup-', [status(thm)], ['17', '27'])).
% 53.94/54.17  thf('29', plain,
% 53.94/54.17      (![X11 : $i, X12 : $i]:
% 53.94/54.17         ((r1_tsep_1 @ X11 @ X12) | ~ (zip_tseitin_0 @ X12 @ X11))),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 53.94/54.17  thf('30', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (zip_tseitin_1 @ sk_E @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_E))),
% 53.94/54.17      inference('sup-', [status(thm)], ['28', '29'])).
% 53.94/54.17  thf('31', plain,
% 53.94/54.17      (![X13 : $i, X14 : $i]:
% 53.94/54.17         (~ (r1_tsep_1 @ X14 @ X13) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 53.94/54.17  thf('32', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (zip_tseitin_1 @ sk_E @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | ~ (zip_tseitin_1 @ sk_B @ sk_E))),
% 53.94/54.17      inference('sup-', [status(thm)], ['30', '31'])).
% 53.94/54.17  thf('33', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (zip_tseitin_1 @ sk_E @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['16', '32'])).
% 53.94/54.17  thf('34', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_D)
% 53.94/54.17        | (zip_tseitin_1 @ sk_E @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('simplify', [status(thm)], ['33'])).
% 53.94/54.17  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf(dt_k2_tsep_1, axiom,
% 53.94/54.17    (![A:$i,B:$i,C:$i]:
% 53.94/54.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 53.94/54.17         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 53.94/54.17         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.94/54.17       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 53.94/54.17         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 53.94/54.17         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 53.94/54.17  thf('37', plain,
% 53.94/54.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X8 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X8)
% 53.94/54.17          | ~ (l1_pre_topc @ X9)
% 53.94/54.17          | (v2_struct_0 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X10)
% 53.94/54.17          | ~ (m1_pre_topc @ X10 @ X9)
% 53.94/54.17          | (m1_pre_topc @ (k2_tsep_1 @ X9 @ X8 @ X10) @ X9))),
% 53.94/54.17      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 53.94/54.17  thf('38', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('sup-', [status(thm)], ['36', '37'])).
% 53.94/54.17  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('40', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('demod', [status(thm)], ['38', '39'])).
% 53.94/54.17  thf('41', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['35', '40'])).
% 53.94/54.17  thf('42', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('43', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('44', plain,
% 53.94/54.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X8 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X8)
% 53.94/54.17          | ~ (l1_pre_topc @ X9)
% 53.94/54.17          | (v2_struct_0 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X10)
% 53.94/54.17          | ~ (m1_pre_topc @ X10 @ X9)
% 53.94/54.17          | (m1_pre_topc @ (k2_tsep_1 @ X9 @ X8 @ X10) @ X9))),
% 53.94/54.17      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 53.94/54.17  thf('45', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_D))),
% 53.94/54.17      inference('sup-', [status(thm)], ['43', '44'])).
% 53.94/54.17  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('47', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_D))),
% 53.94/54.17      inference('demod', [status(thm)], ['45', '46'])).
% 53.94/54.17  thf('48', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['42', '47'])).
% 53.94/54.17  thf('49', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('50', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('51', plain,
% 53.94/54.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X8 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X8)
% 53.94/54.17          | ~ (l1_pre_topc @ X9)
% 53.94/54.17          | (v2_struct_0 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X10)
% 53.94/54.17          | ~ (m1_pre_topc @ X10 @ X9)
% 53.94/54.17          | (v1_pre_topc @ (k2_tsep_1 @ X9 @ X8 @ X10)))),
% 53.94/54.17      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 53.94/54.17  thf('52', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_D))),
% 53.94/54.17      inference('sup-', [status(thm)], ['50', '51'])).
% 53.94/54.17  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('54', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_D))),
% 53.94/54.17      inference('demod', [status(thm)], ['52', '53'])).
% 53.94/54.17  thf('55', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E)))),
% 53.94/54.17      inference('sup-', [status(thm)], ['49', '54'])).
% 53.94/54.17  thf('56', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['42', '47'])).
% 53.94/54.17  thf(d5_tsep_1, axiom,
% 53.94/54.17    (![A:$i]:
% 53.94/54.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 53.94/54.17       ( ![B:$i]:
% 53.94/54.17         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 53.94/54.17           ( ![C:$i]:
% 53.94/54.17             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.94/54.17               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 53.94/54.17                 ( ![D:$i]:
% 53.94/54.17                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 53.94/54.17                       ( m1_pre_topc @ D @ A ) ) =>
% 53.94/54.17                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 53.94/54.17                       ( ( u1_struct_0 @ D ) =
% 53.94/54.17                         ( k3_xboole_0 @
% 53.94/54.17                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 53.94/54.17  thf('57', plain,
% 53.94/54.17      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 53.94/54.17         ((v2_struct_0 @ X4)
% 53.94/54.17          | ~ (m1_pre_topc @ X4 @ X5)
% 53.94/54.17          | (r1_tsep_1 @ X4 @ X6)
% 53.94/54.17          | (v2_struct_0 @ X7)
% 53.94/54.17          | ~ (v1_pre_topc @ X7)
% 53.94/54.17          | ~ (m1_pre_topc @ X7 @ X5)
% 53.94/54.17          | ((X7) != (k2_tsep_1 @ X5 @ X4 @ X6))
% 53.94/54.17          | ((u1_struct_0 @ X7)
% 53.94/54.17              = (k3_xboole_0 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X6)))
% 53.94/54.17          | ~ (m1_pre_topc @ X6 @ X5)
% 53.94/54.17          | (v2_struct_0 @ X6)
% 53.94/54.17          | ~ (l1_pre_topc @ X5)
% 53.94/54.17          | (v2_struct_0 @ X5))),
% 53.94/54.17      inference('cnf', [status(esa)], [d5_tsep_1])).
% 53.94/54.17  thf('58', plain,
% 53.94/54.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 53.94/54.17         ((v2_struct_0 @ X5)
% 53.94/54.17          | ~ (l1_pre_topc @ X5)
% 53.94/54.17          | (v2_struct_0 @ X6)
% 53.94/54.17          | ~ (m1_pre_topc @ X6 @ X5)
% 53.94/54.17          | ((u1_struct_0 @ (k2_tsep_1 @ X5 @ X4 @ X6))
% 53.94/54.17              = (k3_xboole_0 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X6)))
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ X5 @ X4 @ X6) @ X5)
% 53.94/54.17          | ~ (v1_pre_topc @ (k2_tsep_1 @ X5 @ X4 @ X6))
% 53.94/54.17          | (v2_struct_0 @ (k2_tsep_1 @ X5 @ X4 @ X6))
% 53.94/54.17          | (r1_tsep_1 @ X4 @ X6)
% 53.94/54.17          | ~ (m1_pre_topc @ X4 @ X5)
% 53.94/54.17          | (v2_struct_0 @ X4))),
% 53.94/54.17      inference('simplify', [status(thm)], ['57'])).
% 53.94/54.17  thf('59', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['56', '58'])).
% 53.94/54.17  thf('60', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('61', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('63', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 53.94/54.17  thf('64', plain,
% 53.94/54.17      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17          = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E))),
% 53.94/54.17      inference('simplify', [status(thm)], ['63'])).
% 53.94/54.17  thf('65', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E))))),
% 53.94/54.17      inference('sup-', [status(thm)], ['55', '64'])).
% 53.94/54.17  thf('66', plain,
% 53.94/54.17      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17          = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E))),
% 53.94/54.17      inference('simplify', [status(thm)], ['65'])).
% 53.94/54.17  thf('67', plain,
% 53.94/54.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X8 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X8)
% 53.94/54.17          | ~ (l1_pre_topc @ X9)
% 53.94/54.17          | (v2_struct_0 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X10)
% 53.94/54.17          | ~ (m1_pre_topc @ X10 @ X9)
% 53.94/54.17          | ~ (v2_struct_0 @ (k2_tsep_1 @ X9 @ X8 @ X10)))),
% 53.94/54.17      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 53.94/54.17  thf('68', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['66', '67'])).
% 53.94/54.17  thf('69', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('71', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('72', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D))),
% 53.94/54.17      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 53.94/54.17  thf('73', plain,
% 53.94/54.17      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17          = (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E))),
% 53.94/54.17      inference('simplify', [status(thm)], ['72'])).
% 53.94/54.17  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('76', plain,
% 53.94/54.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X8 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X8)
% 53.94/54.17          | ~ (l1_pre_topc @ X9)
% 53.94/54.17          | (v2_struct_0 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X10)
% 53.94/54.17          | ~ (m1_pre_topc @ X10 @ X9)
% 53.94/54.17          | (v1_pre_topc @ (k2_tsep_1 @ X9 @ X8 @ X10)))),
% 53.94/54.17      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 53.94/54.17  thf('77', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('sup-', [status(thm)], ['75', '76'])).
% 53.94/54.17  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('79', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ X0)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('demod', [status(thm)], ['77', '78'])).
% 53.94/54.17  thf('80', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 53.94/54.17      inference('sup-', [status(thm)], ['74', '79'])).
% 53.94/54.17  thf('81', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['35', '40'])).
% 53.94/54.17  thf('82', plain,
% 53.94/54.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 53.94/54.17         ((v2_struct_0 @ X5)
% 53.94/54.17          | ~ (l1_pre_topc @ X5)
% 53.94/54.17          | (v2_struct_0 @ X6)
% 53.94/54.17          | ~ (m1_pre_topc @ X6 @ X5)
% 53.94/54.17          | ((u1_struct_0 @ (k2_tsep_1 @ X5 @ X4 @ X6))
% 53.94/54.17              = (k3_xboole_0 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X6)))
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ X5 @ X4 @ X6) @ X5)
% 53.94/54.17          | ~ (v1_pre_topc @ (k2_tsep_1 @ X5 @ X4 @ X6))
% 53.94/54.17          | (v2_struct_0 @ (k2_tsep_1 @ X5 @ X4 @ X6))
% 53.94/54.17          | (r1_tsep_1 @ X4 @ X6)
% 53.94/54.17          | ~ (m1_pre_topc @ X4 @ X5)
% 53.94/54.17          | (v2_struct_0 @ X4))),
% 53.94/54.17      inference('simplify', [status(thm)], ['57'])).
% 53.94/54.17  thf('83', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 53.94/54.17        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['81', '82'])).
% 53.94/54.17  thf('84', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('87', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A))),
% 53.94/54.17      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 53.94/54.17  thf('88', plain,
% 53.94/54.17      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 53.94/54.17        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('simplify', [status(thm)], ['87'])).
% 53.94/54.17  thf('89', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 53.94/54.17      inference('sup-', [status(thm)], ['80', '88'])).
% 53.94/54.17  thf('90', plain,
% 53.94/54.17      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 53.94/54.17        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('simplify', [status(thm)], ['89'])).
% 53.94/54.17  thf('91', plain,
% 53.94/54.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X8 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X8)
% 53.94/54.17          | ~ (l1_pre_topc @ X9)
% 53.94/54.17          | (v2_struct_0 @ X9)
% 53.94/54.17          | (v2_struct_0 @ X10)
% 53.94/54.17          | ~ (m1_pre_topc @ X10 @ X9)
% 53.94/54.17          | ~ (v2_struct_0 @ (k2_tsep_1 @ X9 @ X8 @ X10)))),
% 53.94/54.17      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 53.94/54.17  thf('92', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 53.94/54.17        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 53.94/54.17      inference('sup-', [status(thm)], ['90', '91'])).
% 53.94/54.17  thf('93', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('95', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('96', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 53.94/54.17        | (v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 53.94/54.17  thf('97', plain,
% 53.94/54.17      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 53.94/54.17          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('simplify', [status(thm)], ['96'])).
% 53.94/54.17  thf(t4_tsep_1, axiom,
% 53.94/54.17    (![A:$i]:
% 53.94/54.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 53.94/54.17       ( ![B:$i]:
% 53.94/54.17         ( ( m1_pre_topc @ B @ A ) =>
% 53.94/54.17           ( ![C:$i]:
% 53.94/54.17             ( ( m1_pre_topc @ C @ A ) =>
% 53.94/54.17               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 53.94/54.17                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 53.94/54.17  thf('98', plain,
% 53.94/54.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X19 @ X20)
% 53.94/54.17          | ~ (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))
% 53.94/54.17          | (m1_pre_topc @ X19 @ X21)
% 53.94/54.17          | ~ (m1_pre_topc @ X21 @ X20)
% 53.94/54.17          | ~ (l1_pre_topc @ X20)
% 53.94/54.17          | ~ (v2_pre_topc @ X20))),
% 53.94/54.17      inference('cnf', [status(esa)], [t4_tsep_1])).
% 53.94/54.17  thf('99', plain,
% 53.94/54.17      (![X0 : $i, X1 : $i]:
% 53.94/54.17         (~ (r1_tarski @ 
% 53.94/54.17             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 53.94/54.17             (u1_struct_0 @ X0))
% 53.94/54.17          | (v2_struct_0 @ sk_C)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_B)
% 53.94/54.17          | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17          | ~ (v2_pre_topc @ X1)
% 53.94/54.17          | ~ (l1_pre_topc @ X1)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ X1)
% 53.94/54.17          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 53.94/54.17      inference('sup-', [status(thm)], ['97', '98'])).
% 53.94/54.17  thf('100', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         (~ (r1_tarski @ 
% 53.94/54.17             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 53.94/54.17             (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))
% 53.94/54.17          | (v2_struct_0 @ sk_E)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_D)
% 53.94/54.17          | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 53.94/54.17          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17             (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 53.94/54.17          | ~ (l1_pre_topc @ X0)
% 53.94/54.17          | ~ (v2_pre_topc @ X0)
% 53.94/54.17          | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17          | (v2_struct_0 @ sk_B)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['73', '99'])).
% 53.94/54.17  thf('101', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('103', plain,
% 53.94/54.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X19 @ X20)
% 53.94/54.17          | ~ (m1_pre_topc @ X19 @ X21)
% 53.94/54.17          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))
% 53.94/54.17          | ~ (m1_pre_topc @ X21 @ X20)
% 53.94/54.17          | ~ (l1_pre_topc @ X20)
% 53.94/54.17          | ~ (v2_pre_topc @ X20))),
% 53.94/54.17      inference('cnf', [status(esa)], [t4_tsep_1])).
% 53.94/54.17  thf('104', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         (~ (v2_pre_topc @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ sk_C @ X0))),
% 53.94/54.17      inference('sup-', [status(thm)], ['102', '103'])).
% 53.94/54.17  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('107', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ sk_C @ X0))),
% 53.94/54.17      inference('demod', [status(thm)], ['104', '105', '106'])).
% 53.94/54.17  thf('108', plain,
% 53.94/54.17      ((~ (m1_pre_topc @ sk_C @ sk_E)
% 53.94/54.17        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_E)))),
% 53.94/54.17      inference('sup-', [status(thm)], ['101', '107'])).
% 53.94/54.17  thf('109', plain, ((m1_pre_topc @ sk_C @ sk_E)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('110', plain,
% 53.94/54.17      ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_E))),
% 53.94/54.17      inference('demod', [status(thm)], ['108', '109'])).
% 53.94/54.17  thf('111', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('112', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('113', plain,
% 53.94/54.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X19 @ X20)
% 53.94/54.17          | ~ (m1_pre_topc @ X19 @ X21)
% 53.94/54.17          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X21))
% 53.94/54.17          | ~ (m1_pre_topc @ X21 @ X20)
% 53.94/54.17          | ~ (l1_pre_topc @ X20)
% 53.94/54.17          | ~ (v2_pre_topc @ X20))),
% 53.94/54.17      inference('cnf', [status(esa)], [t4_tsep_1])).
% 53.94/54.17  thf('114', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         (~ (v2_pre_topc @ sk_A)
% 53.94/54.17          | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ sk_B @ X0))),
% 53.94/54.17      inference('sup-', [status(thm)], ['112', '113'])).
% 53.94/54.17  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('117', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         (~ (m1_pre_topc @ X0 @ sk_A)
% 53.94/54.17          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 53.94/54.17          | ~ (m1_pre_topc @ sk_B @ X0))),
% 53.94/54.17      inference('demod', [status(thm)], ['114', '115', '116'])).
% 53.94/54.17  thf('118', plain,
% 53.94/54.17      ((~ (m1_pre_topc @ sk_B @ sk_D)
% 53.94/54.17        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))),
% 53.94/54.17      inference('sup-', [status(thm)], ['111', '117'])).
% 53.94/54.17  thf('119', plain, ((m1_pre_topc @ sk_B @ sk_D)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('120', plain,
% 53.94/54.17      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))),
% 53.94/54.17      inference('demod', [status(thm)], ['118', '119'])).
% 53.94/54.17  thf(t27_xboole_1, axiom,
% 53.94/54.17    (![A:$i,B:$i,C:$i,D:$i]:
% 53.94/54.17     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 53.94/54.17       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 53.94/54.17  thf('121', plain,
% 53.94/54.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.94/54.17         (~ (r1_tarski @ X0 @ X1)
% 53.94/54.17          | ~ (r1_tarski @ X2 @ X3)
% 53.94/54.17          | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X3)))),
% 53.94/54.17      inference('cnf', [status(esa)], [t27_xboole_1])).
% 53.94/54.17  thf('122', plain,
% 53.94/54.17      (![X0 : $i, X1 : $i]:
% 53.94/54.17         ((r1_tarski @ (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ X1) @ 
% 53.94/54.17           (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ X0))
% 53.94/54.17          | ~ (r1_tarski @ X1 @ X0))),
% 53.94/54.17      inference('sup-', [status(thm)], ['120', '121'])).
% 53.94/54.17  thf('123', plain,
% 53.94/54.17      ((r1_tarski @ 
% 53.94/54.17        (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 53.94/54.17        (k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_E)))),
% 53.94/54.17      inference('sup-', [status(thm)], ['110', '122'])).
% 53.94/54.17  thf('124', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_E)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_D)
% 53.94/54.17          | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 53.94/54.17          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17             (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 53.94/54.17          | ~ (l1_pre_topc @ X0)
% 53.94/54.17          | ~ (v2_pre_topc @ X0)
% 53.94/54.17          | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17          | (v2_struct_0 @ sk_B)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('demod', [status(thm)], ['100', '123'])).
% 53.94/54.17  thf('125', plain,
% 53.94/54.17      (![X0 : $i]:
% 53.94/54.17         ((v2_struct_0 @ sk_C)
% 53.94/54.17          | (v2_struct_0 @ sk_B)
% 53.94/54.17          | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17          | ~ (v2_pre_topc @ X0)
% 53.94/54.17          | ~ (l1_pre_topc @ X0)
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 53.94/54.17          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17             (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 53.94/54.17          | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17          | (v2_struct_0 @ sk_D)
% 53.94/54.17          | (v2_struct_0 @ sk_A)
% 53.94/54.17          | (v2_struct_0 @ sk_E))),
% 53.94/54.17      inference('simplify', [status(thm)], ['124'])).
% 53.94/54.17  thf('126', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17           (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | ~ (l1_pre_topc @ sk_A)
% 53.94/54.17        | ~ (v2_pre_topc @ sk_A)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['48', '125'])).
% 53.94/54.17  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('129', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17           (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('demod', [status(thm)], ['126', '127', '128'])).
% 53.94/54.17  thf('130', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17           (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E))),
% 53.94/54.17      inference('simplify', [status(thm)], ['129'])).
% 53.94/54.17  thf('131', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17           (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['41', '130'])).
% 53.94/54.17  thf('132', plain,
% 53.94/54.17      (((r1_tsep_1 @ sk_B @ sk_C)
% 53.94/54.17        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17           (k2_tsep_1 @ sk_A @ sk_D @ sk_E))
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('simplify', [status(thm)], ['131'])).
% 53.94/54.17  thf('133', plain,
% 53.94/54.17      (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ 
% 53.94/54.17          (k2_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('134', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (r1_tsep_1 @ sk_B @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['132', '133'])).
% 53.94/54.17  thf('135', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('136', plain,
% 53.94/54.17      (((r1_tsep_1 @ sk_D @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['134', '135'])).
% 53.94/54.17  thf('137', plain,
% 53.94/54.17      (![X13 : $i, X14 : $i]:
% 53.94/54.17         (~ (r1_tsep_1 @ X13 @ X14) | ~ (zip_tseitin_1 @ X14 @ X13))),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 53.94/54.17  thf('138', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | ~ (zip_tseitin_1 @ sk_E @ sk_D))),
% 53.94/54.17      inference('sup-', [status(thm)], ['136', '137'])).
% 53.94/54.17  thf('139', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('sup-', [status(thm)], ['34', '138'])).
% 53.94/54.17  thf('140', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_D)
% 53.94/54.17        | (v2_struct_0 @ sk_A)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_C))),
% 53.94/54.17      inference('simplify', [status(thm)], ['139'])).
% 53.94/54.17  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('142', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_C)
% 53.94/54.17        | (v2_struct_0 @ sk_B)
% 53.94/54.17        | (v2_struct_0 @ sk_E)
% 53.94/54.17        | (v2_struct_0 @ sk_D))),
% 53.94/54.17      inference('sup-', [status(thm)], ['140', '141'])).
% 53.94/54.17  thf('143', plain, (~ (v2_struct_0 @ sk_C)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('144', plain,
% 53.94/54.17      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_B))),
% 53.94/54.17      inference('sup-', [status(thm)], ['142', '143'])).
% 53.94/54.17  thf('145', plain, (~ (v2_struct_0 @ sk_D)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('146', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_E))),
% 53.94/54.17      inference('clc', [status(thm)], ['144', '145'])).
% 53.94/54.17  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 53.94/54.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.94/54.17  thf('148', plain, ((v2_struct_0 @ sk_E)),
% 53.94/54.17      inference('clc', [status(thm)], ['146', '147'])).
% 53.94/54.17  thf('149', plain, ($false), inference('demod', [status(thm)], ['0', '148'])).
% 53.94/54.17  
% 53.94/54.17  % SZS output end Refutation
% 53.94/54.17  
% 53.94/54.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
