%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eGKd7tBakz

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:18 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  495 (26800 expanded)
%              Number of leaves         :   40 (7264 expanded)
%              Depth                    :   42
%              Number of atoms          : 3865 (448253 expanded)
%              Number of equality atoms :   62 (1874 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(t23_tmap_1,conjecture,(
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
                   => ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) )
                      | ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) )).

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
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) )
                        | ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ( m1_pre_topc @ X37 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['10','11','12'])).

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

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('29',plain,
    ( ~ ( v2_pre_topc @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('32',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('37',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['29','35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('39',plain,(
    m1_pre_topc @ sk_D_2 @ sk_D_2 ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t22_tsep_1,axiom,(
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
             => ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_pre_topc @ X34 @ ( k1_tsep_1 @ X35 @ X34 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ~ ( v2_pre_topc @ sk_D_2 )
      | ~ ( l1_pre_topc @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('43',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_2 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,
    ( ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['25','26'])).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('54',plain,
    ( ~ ( v2_pre_topc @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_D_2 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('56',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('57',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['25','26'])).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('62',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','57','62'])).

thf('64',plain,
    ( ~ ( m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['37','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('66',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['3','66'])).

thf('68',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('69',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_D_2 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) )
    | ~ ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('78',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('79',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
      = ( k2_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) @ sk_D_2 ),
    inference(clc,[status(thm)],['25','26'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_D_2 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('86',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('88',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['81','88'])).

thf('90',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2 ) )
    = ( k2_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['81','88'])).

thf('91',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_D_2 ) )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['73','89','90'])).

thf('92',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ sk_D_2 )
      = ( u1_struct_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','91'])).

thf('93',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('94',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('95',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_struct_0 @ sk_D_2 )
    = ( u1_struct_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['92','93','96'])).

thf('98',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('102',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('107',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('111',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('121',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('124',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('129',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['121','127','128'])).

thf('130',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('131',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('132',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_pre_topc @ X34 @ ( k1_tsep_1 @ X35 @ X34 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','137'])).

thf('139',plain,
    ( ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['117','118'])).

thf('145',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('146',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('148',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('149',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['117','118'])).

thf('151',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('152',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('154',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['143','149','154'])).

thf('156',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['129','155'])).

thf('157',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('158',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['99','158'])).

thf('160',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('161',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('162',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','162'])).

thf('164',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['117','118'])).

thf('165',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('168',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('170',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('172',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    m1_pre_topc @ sk_B @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('174',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('175',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('177',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('178',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','178'])).

thf('180',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['163','179'])).

thf('181',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('182',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','182'])).

thf('184',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('185',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('186',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('187',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['183','184','187'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('189',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ( r1_tsep_1 @ X28 @ X27 )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['185','186'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['97','192'])).

thf('194',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('195',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('197',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('198',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['198'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('200',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('201',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('203',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('205',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('209',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['201','202','209'])).

thf('211',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('212',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('214',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['207','208'])).

thf('215',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['197','215'])).

thf('217',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('218',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['196','218'])).

thf('220',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['207','208'])).

thf('221',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('225',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['222','233'])).

thf('235',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['236','237'])).

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

thf('239',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( v1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( X25
       != ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( ( u1_struct_0 @ X25 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('240',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['238','240'])).

thf('242',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('243',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['241','242','243','244'])).

thf('246',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('248',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('249',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['236','237'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('251',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('254',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('258',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('259',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['251','257','258'])).

thf('260',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('262',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_pre_topc @ X34 @ ( k1_tsep_1 @ X35 @ X34 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t22_tsep_1])).

thf('263',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('265',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['260','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['236','237'])).

thf('276',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('277',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('279',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('280',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['277','278','279'])).

thf('281',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['236','237'])).

thf('282',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('283',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('285',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['274','280','285'])).

thf('287',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['259','286'])).

thf('288',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('289',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('290',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['248','289'])).

thf('291',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['207','208'])).

thf('292',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('294',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['247','294'])).

thf('296',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('297',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('298',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['296','297'])).

thf('299',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('300',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('301',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('303',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['236','237'])).

thf('305',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('306',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('308',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['306','307'])).

thf('309',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('310',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['308','309'])).

thf('311',plain,
    ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['303','310'])).

thf('312',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('313',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('314',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('315',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['295','311','312','315'])).

thf('317',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('318',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('319',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('321',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['319','320'])).

thf('322',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['322','323'])).

thf('325',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('326',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['324','325'])).

thf('327',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('328',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('329',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['326','327','328'])).

thf('330',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('331',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('332',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['330','331'])).

thf('333',plain,
    ( ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['333','334'])).

thf('336',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X39 )
      | ( r1_tarski @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('337',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['335','336'])).

thf('338',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['322','323'])).

thf('339',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('340',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['338','339'])).

thf('341',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('342',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('343',plain,(
    v2_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['340','341','342'])).

thf('344',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['322','323'])).

thf('345',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('346',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['344','345'])).

thf('347',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('348',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('349',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['337','343','348'])).

thf('350',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['329','349'])).

thf('351',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['333','334'])).

thf('352',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['350','351'])).

thf('353',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['318','352'])).

thf('354',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('355',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('356',plain,(
    l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['354','355'])).

thf('357',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['353','356'])).

thf('358',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['322','323'])).

thf('359',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('360',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['358','359'])).

thf('361',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('362',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['360','361'])).

thf('363',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('364',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['362','363'])).

thf('365',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('366',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,(
    m1_pre_topc @ sk_C_1 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['333','334'])).

thf('368',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('369',plain,
    ( ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,(
    l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('371',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('372',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['369','370','371'])).

thf('373',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['366','372'])).

thf('374',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['357','373'])).

thf('375',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('376',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['374','375'])).

thf('377',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['317','376'])).

thf('378',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('379',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['207','208'])).

thf('380',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['377','378','379'])).

thf('381',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['183','184','187'])).

thf('382',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('384',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('385',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['383','384'])).

thf('386',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('387',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['385','386'])).

thf('388',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['387'])).

thf('389',plain,
    ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['382','388'])).

thf('390',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('391',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['389','390'])).

thf('392',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('393',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['391','392'])).

thf('394',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['246','316','380','381','393'])).

thf('395',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('396',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['394','395'])).

thf('397',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['205','206'])).

thf('399',plain,(
    m1_pre_topc @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('400',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['396','397','398','399'])).

thf('401',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['400'])).

thf('402',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['401','402'])).

thf('404',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['403','404'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('406',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X3 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('407',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['405','406'])).

thf('408',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['221','407'])).

thf('409',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('410',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('411',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['198'])).

thf('412',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('413',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['411','412'])).

thf('414',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('415',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['207','208'])).

thf('416',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['413','414','415'])).

thf('417',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['410','416'])).

thf('418',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('419',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['417','418'])).

thf('420',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['409','419'])).

thf('421',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['207','208'])).

thf('422',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['420','421'])).

thf('423',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['405','406'])).

thf('424',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['422','423'])).

thf('425',plain,
    ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('426',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['424','425'])).

thf('427',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('428',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['426','427'])).

thf('429',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['185','186'])).

thf('430',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('431',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['428','429','430'])).

thf('432',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('433',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['431','432'])).

thf('434',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['424','425'])).

thf('435',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('436',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['434','435'])).

thf('437',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('438',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['198'])).

thf('439',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['433','436','437','438'])).

thf('440',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['408','439'])).

thf('441',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['195','440'])).

thf('442',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_struct_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( r1_tsep_1 @ X33 @ X32 )
      | ~ ( r1_tsep_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('443',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['441','442'])).

thf('444',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['185','186'])).

thf('445',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('446',plain,(
    r1_tsep_1 @ sk_B @ sk_D_2 ),
    inference(demod,[status(thm)],['443','444','445'])).

thf('447',plain,
    ( $false
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['1','446'])).

thf('448',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['195','440'])).

thf('449',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('450',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['448','449'])).

thf('451',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('452',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['450','451'])).

thf('453',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['447','452'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eGKd7tBakz
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.20  % Solved by: fo/fo7.sh
% 0.99/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.20  % done 1689 iterations in 0.731s
% 0.99/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.20  % SZS output start Refutation
% 0.99/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.20  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.99/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.99/1.20  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.99/1.20  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.99/1.20  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.99/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.99/1.20  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.99/1.20  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.20  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.99/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.20  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.99/1.20  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.99/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.20  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.99/1.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.99/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.20  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.99/1.20  thf(t23_tmap_1, conjecture,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.99/1.20           ( ![C:$i]:
% 0.99/1.20             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.99/1.20               ( ![D:$i]:
% 0.99/1.20                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.99/1.20                   ( ( m1_pre_topc @ B @ C ) =>
% 0.99/1.20                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.99/1.20                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.99/1.20                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.99/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.20    (~( ![A:$i]:
% 0.99/1.20        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.99/1.20            ( l1_pre_topc @ A ) ) =>
% 0.99/1.20          ( ![B:$i]:
% 0.99/1.20            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.99/1.20              ( ![C:$i]:
% 0.99/1.20                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.99/1.20                  ( ![D:$i]:
% 0.99/1.20                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.99/1.20                      ( ( m1_pre_topc @ B @ C ) =>
% 0.99/1.20                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.99/1.20                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.99/1.20                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.99/1.20    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.99/1.20  thf('0', plain,
% 0.99/1.20      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('1', plain,
% 0.99/1.20      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.99/1.20      inference('split', [status(esa)], ['0'])).
% 0.99/1.20  thf(d3_struct_0, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.99/1.20  thf('2', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('3', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('4', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(d10_xboole_0, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.20  thf('5', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.99/1.20      inference('simplify', [status(thm)], ['5'])).
% 0.99/1.20  thf(t4_tsep_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_pre_topc @ B @ A ) =>
% 0.99/1.20           ( ![C:$i]:
% 0.99/1.20             ( ( m1_pre_topc @ C @ A ) =>
% 0.99/1.20               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.99/1.20                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.99/1.20  thf('7', plain,
% 0.99/1.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X37 @ X38)
% 0.99/1.20          | ~ (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.99/1.20          | (m1_pre_topc @ X37 @ X39)
% 0.99/1.20          | ~ (m1_pre_topc @ X39 @ X38)
% 0.99/1.20          | ~ (l1_pre_topc @ X38)
% 0.99/1.20          | ~ (v2_pre_topc @ X38))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.99/1.20  thf('8', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (~ (v2_pre_topc @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | (m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['6', '7'])).
% 0.99/1.20  thf('9', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.20  thf('10', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_A)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | (m1_pre_topc @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['4', '9'])).
% 0.99/1.20  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('13', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.99/1.20  thf('14', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.99/1.20  thf(dt_k1_tsep_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.99/1.20         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.99/1.20         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.99/1.20       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.99/1.20         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 0.99/1.20         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.99/1.20  thf('15', plain,
% 0.99/1.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X29 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X29)
% 0.99/1.20          | ~ (l1_pre_topc @ X30)
% 0.99/1.20          | (v2_struct_0 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X31)
% 0.99/1.20          | ~ (m1_pre_topc @ X31 @ X30)
% 0.99/1.20          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.99/1.20  thf('16', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_D_2)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['14', '15'])).
% 0.99/1.20  thf('17', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(dt_m1_pre_topc, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.99/1.20  thf('18', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X21 @ X22)
% 0.99/1.20          | (l1_pre_topc @ X21)
% 0.99/1.20          | ~ (l1_pre_topc @ X22))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.99/1.20  thf('19', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['17', '18'])).
% 0.99/1.20  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('21', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('22', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['16', '21'])).
% 0.99/1.20  thf('23', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.99/1.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0) @ sk_D_2))),
% 0.99/1.20      inference('simplify', [status(thm)], ['22'])).
% 0.99/1.20  thf('24', plain,
% 0.99/1.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)
% 0.99/1.20        | (v2_struct_0 @ sk_D_2)
% 0.99/1.20        | (v2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['13', '23'])).
% 0.99/1.20  thf('25', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_D_2)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2))),
% 0.99/1.20      inference('simplify', [status(thm)], ['24'])).
% 0.99/1.20  thf('26', plain, (~ (v2_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('27', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.99/1.20      inference('clc', [status(thm)], ['25', '26'])).
% 0.99/1.20  thf('28', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.20  thf('29', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_D_2)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_D_2)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ 
% 0.99/1.20           (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['27', '28'])).
% 0.99/1.20  thf('30', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(cc1_pre_topc, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.99/1.20  thf('31', plain,
% 0.99/1.20      (![X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X7 @ X8)
% 0.99/1.20          | (v2_pre_topc @ X7)
% 0.99/1.20          | ~ (l1_pre_topc @ X8)
% 0.99/1.20          | ~ (v2_pre_topc @ X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.99/1.20  thf('32', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_A)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | (v2_pre_topc @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['30', '31'])).
% 0.99/1.20  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('35', plain, ((v2_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.99/1.20  thf('36', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('37', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ 
% 0.99/1.20        (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['29', '35', '36'])).
% 0.99/1.20  thf('38', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.99/1.20  thf('39', plain, ((m1_pre_topc @ sk_D_2 @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.99/1.20  thf(t22_tsep_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.99/1.20           ( ![C:$i]:
% 0.99/1.20             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.99/1.20               ( m1_pre_topc @ B @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.99/1.20  thf('40', plain,
% 0.99/1.20      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.99/1.20         ((v2_struct_0 @ X34)
% 0.99/1.20          | ~ (m1_pre_topc @ X34 @ X35)
% 0.99/1.20          | (m1_pre_topc @ X34 @ (k1_tsep_1 @ X35 @ X34 @ X36))
% 0.99/1.20          | ~ (m1_pre_topc @ X36 @ X35)
% 0.99/1.20          | (v2_struct_0 @ X36)
% 0.99/1.20          | ~ (l1_pre_topc @ X35)
% 0.99/1.20          | ~ (v2_pre_topc @ X35)
% 0.99/1.20          | (v2_struct_0 @ X35))),
% 0.99/1.20      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.99/1.20  thf('41', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_D_2)
% 0.99/1.20          | ~ (v2_pre_topc @ sk_D_2)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.99/1.20          | (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 0.99/1.20          | (v2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['39', '40'])).
% 0.99/1.20  thf('42', plain, ((v2_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.99/1.20  thf('43', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('44', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.99/1.20          | (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 0.99/1.20          | (v2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.99/1.20  thf('45', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_D_2)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('simplify', [status(thm)], ['44'])).
% 0.99/1.20  thf('46', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_D_2)
% 0.99/1.20        | (v2_struct_0 @ sk_D_2)
% 0.99/1.20        | (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['38', '45'])).
% 0.99/1.20  thf('47', plain,
% 0.99/1.20      (((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20        | (v2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('simplify', [status(thm)], ['46'])).
% 0.99/1.20  thf('48', plain, (~ (v2_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('49', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('clc', [status(thm)], ['47', '48'])).
% 0.99/1.20  thf('50', plain,
% 0.99/1.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X37 @ X38)
% 0.99/1.20          | ~ (m1_pre_topc @ X37 @ X39)
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.99/1.20          | ~ (m1_pre_topc @ X39 @ X38)
% 0.99/1.20          | ~ (l1_pre_topc @ X38)
% 0.99/1.20          | ~ (v2_pre_topc @ X38))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.99/1.20  thf('51', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_D_2 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.20  thf('52', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.99/1.20      inference('clc', [status(thm)], ['25', '26'])).
% 0.99/1.20  thf('53', plain,
% 0.99/1.20      (![X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X7 @ X8)
% 0.99/1.20          | (v2_pre_topc @ X7)
% 0.99/1.20          | ~ (l1_pre_topc @ X8)
% 0.99/1.20          | ~ (v2_pre_topc @ X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.99/1.20  thf('54', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_D_2)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_D_2)
% 0.99/1.20        | (v2_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['52', '53'])).
% 0.99/1.20  thf('55', plain, ((v2_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.99/1.20  thf('56', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('57', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.99/1.20  thf('58', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.99/1.20      inference('clc', [status(thm)], ['25', '26'])).
% 0.99/1.20  thf('59', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X21 @ X22)
% 0.99/1.20          | (l1_pre_topc @ X21)
% 0.99/1.20          | ~ (l1_pre_topc @ X22))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.99/1.20  thf('60', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_D_2)
% 0.99/1.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['58', '59'])).
% 0.99/1.20  thf('61', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('62', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['60', '61'])).
% 0.99/1.20  thf('63', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_D_2 @ X0))),
% 0.99/1.20      inference('demod', [status(thm)], ['51', '57', '62'])).
% 0.99/1.20  thf('64', plain,
% 0.99/1.20      ((~ (m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20        | (r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.99/1.20           (u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['37', '63'])).
% 0.99/1.20  thf('65', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('clc', [status(thm)], ['47', '48'])).
% 0.99/1.20  thf('66', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.99/1.20        (u1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['64', '65'])).
% 0.99/1.20  thf('67', plain,
% 0.99/1.20      (((r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.99/1.20         (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))
% 0.99/1.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['3', '66'])).
% 0.99/1.20  thf('68', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['60', '61'])).
% 0.99/1.20  thf(dt_l1_pre_topc, axiom,
% 0.99/1.20    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.99/1.20  thf('69', plain,
% 0.99/1.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('70', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['68', '69'])).
% 0.99/1.20  thf('71', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_D_2) @ 
% 0.99/1.20        (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['67', '70'])).
% 0.99/1.20  thf('72', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('73', plain,
% 0.99/1.20      ((~ (r1_tarski @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.99/1.20           (u1_struct_0 @ sk_D_2))
% 0.99/1.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20            = (u1_struct_0 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['71', '72'])).
% 0.99/1.20  thf('74', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_D_2 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('clc', [status(thm)], ['47', '48'])).
% 0.99/1.20  thf(d9_pre_topc, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( l1_pre_topc @ B ) =>
% 0.99/1.20           ( ( m1_pre_topc @ B @ A ) <=>
% 0.99/1.20             ( ( ![C:$i]:
% 0.99/1.20                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.99/1.20                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.99/1.20                     ( ?[D:$i]:
% 0.99/1.20                       ( ( m1_subset_1 @
% 0.99/1.20                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.99/1.20                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.20                         ( ( C ) =
% 0.99/1.20                           ( k9_subset_1 @
% 0.99/1.20                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.99/1.20               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.99/1.20  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.99/1.20  thf(zf_stmt_2, axiom,
% 0.99/1.20    (![D:$i,C:$i,B:$i,A:$i]:
% 0.99/1.20     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.99/1.20       ( ( ( C ) =
% 0.99/1.20           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.99/1.20         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.99/1.20  thf(zf_stmt_3, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( l1_pre_topc @ B ) =>
% 0.99/1.20           ( ( m1_pre_topc @ B @ A ) <=>
% 0.99/1.20             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.99/1.20               ( ![C:$i]:
% 0.99/1.20                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.99/1.20                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.99/1.20                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.99/1.20  thf('75', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('76', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20        | (r1_tarski @ (k2_struct_0 @ sk_D_2) @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))
% 0.99/1.20        | ~ (l1_pre_topc @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['74', '75'])).
% 0.99/1.20  thf('77', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['60', '61'])).
% 0.99/1.20  thf('78', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('79', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ sk_D_2) @ 
% 0.99/1.20        (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.99/1.20  thf('80', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('81', plain,
% 0.99/1.20      ((~ (r1_tarski @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_D_2))
% 0.99/1.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20            = (k2_struct_0 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['79', '80'])).
% 0.99/1.20  thf('82', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2) @ sk_D_2)),
% 0.99/1.20      inference('clc', [status(thm)], ['25', '26'])).
% 0.99/1.20  thf('83', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('84', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_D_2)
% 0.99/1.20        | (r1_tarski @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_D_2))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['82', '83'])).
% 0.99/1.20  thf('85', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('86', plain,
% 0.99/1.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.99/1.20         (k2_struct_0 @ sk_D_2))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['84', '85'])).
% 0.99/1.20  thf('87', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['60', '61'])).
% 0.99/1.20  thf('88', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2)) @ 
% 0.99/1.20        (k2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['86', '87'])).
% 0.99/1.20  thf('89', plain,
% 0.99/1.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20         = (k2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['81', '88'])).
% 0.99/1.20  thf('90', plain,
% 0.99/1.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_D_2 @ sk_D_2 @ sk_D_2))
% 0.99/1.20         = (k2_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['81', '88'])).
% 0.99/1.20  thf('91', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_D_2))
% 0.99/1.20        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['73', '89', '90'])).
% 0.99/1.20  thf('92', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_D_2))
% 0.99/1.20        | ~ (l1_struct_0 @ sk_D_2)
% 0.99/1.20        | ((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['2', '91'])).
% 0.99/1.20  thf('93', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.99/1.20      inference('simplify', [status(thm)], ['5'])).
% 0.99/1.20  thf('94', plain, ((l1_pre_topc @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['19', '20'])).
% 0.99/1.20  thf('95', plain,
% 0.99/1.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('96', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('97', plain, (((k2_struct_0 @ sk_D_2) = (u1_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('demod', [status(thm)], ['92', '93', '96'])).
% 0.99/1.20  thf('98', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('99', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('100', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('101', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.20  thf('102', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_A)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | (m1_pre_topc @ sk_B @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['100', '101'])).
% 0.99/1.20  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('105', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.99/1.20  thf('106', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.99/1.20  thf('107', plain,
% 0.99/1.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X29 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X29)
% 0.99/1.20          | ~ (l1_pre_topc @ X30)
% 0.99/1.20          | (v2_struct_0 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X31)
% 0.99/1.20          | ~ (m1_pre_topc @ X31 @ X30)
% 0.99/1.20          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.99/1.20  thf('108', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_B)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['106', '107'])).
% 0.99/1.20  thf('109', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('110', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X21 @ X22)
% 0.99/1.20          | (l1_pre_topc @ X21)
% 0.99/1.20          | ~ (l1_pre_topc @ X22))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.99/1.20  thf('111', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['109', '110'])).
% 0.99/1.20  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('113', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('114', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['108', '113'])).
% 0.99/1.20  thf('115', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.99/1.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ X0) @ sk_B))),
% 0.99/1.20      inference('simplify', [status(thm)], ['114'])).
% 0.99/1.20  thf('116', plain,
% 0.99/1.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['105', '115'])).
% 0.99/1.20  thf('117', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_B)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B))),
% 0.99/1.20      inference('simplify', [status(thm)], ['116'])).
% 0.99/1.20  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('119', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.99/1.20      inference('clc', [status(thm)], ['117', '118'])).
% 0.99/1.20  thf('120', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.20  thf('121', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_B)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_B)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ 
% 0.99/1.20           (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['119', '120'])).
% 0.99/1.20  thf('122', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('123', plain,
% 0.99/1.20      (![X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X7 @ X8)
% 0.99/1.20          | (v2_pre_topc @ X7)
% 0.99/1.20          | ~ (l1_pre_topc @ X8)
% 0.99/1.20          | ~ (v2_pre_topc @ X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.99/1.20  thf('124', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['122', '123'])).
% 0.99/1.20  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('127', plain, ((v2_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.99/1.20  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('129', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ 
% 0.99/1.20        (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['121', '127', '128'])).
% 0.99/1.20  thf('130', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.99/1.20  thf('131', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.99/1.20  thf('132', plain,
% 0.99/1.20      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.99/1.20         ((v2_struct_0 @ X34)
% 0.99/1.20          | ~ (m1_pre_topc @ X34 @ X35)
% 0.99/1.20          | (m1_pre_topc @ X34 @ (k1_tsep_1 @ X35 @ X34 @ X36))
% 0.99/1.20          | ~ (m1_pre_topc @ X36 @ X35)
% 0.99/1.20          | (v2_struct_0 @ X36)
% 0.99/1.20          | ~ (l1_pre_topc @ X35)
% 0.99/1.20          | ~ (v2_pre_topc @ X35)
% 0.99/1.20          | (v2_struct_0 @ X35))),
% 0.99/1.20      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.99/1.20  thf('133', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_B)
% 0.99/1.20          | ~ (v2_pre_topc @ sk_B)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.99/1.20          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 0.99/1.20          | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['131', '132'])).
% 0.99/1.20  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.99/1.20  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('136', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.99/1.20          | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 0.99/1.20          | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.99/1.20  thf('137', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('simplify', [status(thm)], ['136'])).
% 0.99/1.20  thf('138', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['130', '137'])).
% 0.99/1.20  thf('139', plain,
% 0.99/1.20      (((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.99/1.20        | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('simplify', [status(thm)], ['138'])).
% 0.99/1.20  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('141', plain, ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['139', '140'])).
% 0.99/1.20  thf('142', plain,
% 0.99/1.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X37 @ X38)
% 0.99/1.20          | ~ (m1_pre_topc @ X37 @ X39)
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.99/1.20          | ~ (m1_pre_topc @ X39 @ X38)
% 0.99/1.20          | ~ (l1_pre_topc @ X38)
% 0.99/1.20          | ~ (v2_pre_topc @ X38))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.99/1.20  thf('143', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.99/1.20          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['141', '142'])).
% 0.99/1.20  thf('144', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.99/1.20      inference('clc', [status(thm)], ['117', '118'])).
% 0.99/1.20  thf('145', plain,
% 0.99/1.20      (![X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X7 @ X8)
% 0.99/1.20          | (v2_pre_topc @ X7)
% 0.99/1.20          | ~ (l1_pre_topc @ X8)
% 0.99/1.20          | ~ (v2_pre_topc @ X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.99/1.20  thf('146', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_B)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_B)
% 0.99/1.20        | (v2_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['144', '145'])).
% 0.99/1.20  thf('147', plain, ((v2_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.99/1.20  thf('148', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('149', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.99/1.20  thf('150', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.99/1.20      inference('clc', [status(thm)], ['117', '118'])).
% 0.99/1.20  thf('151', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X21 @ X22)
% 0.99/1.20          | (l1_pre_topc @ X21)
% 0.99/1.20          | ~ (l1_pre_topc @ X22))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.99/1.20  thf('152', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_B)
% 0.99/1.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['150', '151'])).
% 0.99/1.20  thf('153', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('154', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['152', '153'])).
% 0.99/1.20  thf('155', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.99/1.20      inference('demod', [status(thm)], ['143', '149', '154'])).
% 0.99/1.20  thf('156', plain,
% 0.99/1.20      ((~ (m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.99/1.20        | (r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.99/1.20           (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['129', '155'])).
% 0.99/1.20  thf('157', plain, ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['139', '140'])).
% 0.99/1.20  thf('158', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.99/1.20        (u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['156', '157'])).
% 0.99/1.20  thf('159', plain,
% 0.99/1.20      (((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.99/1.20         (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 0.99/1.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['99', '158'])).
% 0.99/1.20  thf('160', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['152', '153'])).
% 0.99/1.20  thf('161', plain,
% 0.99/1.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('162', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['160', '161'])).
% 0.99/1.20  thf('163', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 0.99/1.20        (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['159', '162'])).
% 0.99/1.20  thf('164', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.99/1.20      inference('clc', [status(thm)], ['117', '118'])).
% 0.99/1.20  thf('165', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('166', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_B)
% 0.99/1.20        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_B))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['164', '165'])).
% 0.99/1.20  thf('167', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('168', plain,
% 0.99/1.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 0.99/1.20         (k2_struct_0 @ sk_B))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['166', '167'])).
% 0.99/1.20  thf('169', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['152', '153'])).
% 0.99/1.20  thf('170', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)) @ 
% 0.99/1.20        (k2_struct_0 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['168', '169'])).
% 0.99/1.20  thf('171', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('172', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 0.99/1.20        | ((k2_struct_0 @ sk_B)
% 0.99/1.20            = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['170', '171'])).
% 0.99/1.20  thf('173', plain, ((m1_pre_topc @ sk_B @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['139', '140'])).
% 0.99/1.20  thf('174', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('175', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.99/1.20        | (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))
% 0.99/1.20        | ~ (l1_pre_topc @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['173', '174'])).
% 0.99/1.20  thf('176', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['152', '153'])).
% 0.99/1.20  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('178', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 0.99/1.20        (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.99/1.20  thf('179', plain,
% 0.99/1.20      (((k2_struct_0 @ sk_B) = (k2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['172', '178'])).
% 0.99/1.20  thf('180', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['163', '179'])).
% 0.99/1.20  thf('181', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('182', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.99/1.20        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['180', '181'])).
% 0.99/1.20  thf('183', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.99/1.20        | ~ (l1_struct_0 @ sk_B)
% 0.99/1.20        | ((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['98', '182'])).
% 0.99/1.20  thf('184', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.99/1.20      inference('simplify', [status(thm)], ['5'])).
% 0.99/1.20  thf('185', plain, ((l1_pre_topc @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['111', '112'])).
% 0.99/1.20  thf('186', plain,
% 0.99/1.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('187', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.20      inference('sup-', [status(thm)], ['185', '186'])).
% 0.99/1.20  thf('188', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['183', '184', '187'])).
% 0.99/1.20  thf(d3_tsep_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_struct_0 @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( l1_struct_0 @ B ) =>
% 0.99/1.20           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.99/1.20             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.99/1.20  thf('189', plain,
% 0.99/1.20      (![X27 : $i, X28 : $i]:
% 0.99/1.20         (~ (l1_struct_0 @ X27)
% 0.99/1.20          | ~ (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.99/1.20          | (r1_tsep_1 @ X28 @ X27)
% 0.99/1.20          | ~ (l1_struct_0 @ X28))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.99/1.20  thf('190', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 0.99/1.20          | ~ (l1_struct_0 @ X0)
% 0.99/1.20          | (r1_tsep_1 @ X0 @ sk_B)
% 0.99/1.20          | ~ (l1_struct_0 @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['188', '189'])).
% 0.99/1.20  thf('191', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.20      inference('sup-', [status(thm)], ['185', '186'])).
% 0.99/1.20  thf('192', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_B))
% 0.99/1.20          | ~ (l1_struct_0 @ X0)
% 0.99/1.20          | (r1_tsep_1 @ X0 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['190', '191'])).
% 0.99/1.20  thf('193', plain,
% 0.99/1.20      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 0.99/1.20        | (r1_tsep_1 @ sk_D_2 @ sk_B)
% 0.99/1.20        | ~ (l1_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['97', '192'])).
% 0.99/1.20  thf('194', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('195', plain,
% 0.99/1.20      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 0.99/1.20        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['193', '194'])).
% 0.99/1.20  thf('196', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('197', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('198', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('199', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('split', [status(esa)], ['198'])).
% 0.99/1.20  thf(symmetry_r1_tsep_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.99/1.20       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.99/1.20  thf('200', plain,
% 0.99/1.20      (![X32 : $i, X33 : $i]:
% 0.99/1.20         (~ (l1_struct_0 @ X32)
% 0.99/1.20          | ~ (l1_struct_0 @ X33)
% 0.99/1.20          | (r1_tsep_1 @ X33 @ X32)
% 0.99/1.20          | ~ (r1_tsep_1 @ X32 @ X33))),
% 0.99/1.20      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.99/1.20  thf('201', plain,
% 0.99/1.20      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 0.99/1.20         | ~ (l1_struct_0 @ sk_D_2)
% 0.99/1.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['199', '200'])).
% 0.99/1.20  thf('202', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('203', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('204', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X21 @ X22)
% 0.99/1.20          | (l1_pre_topc @ X21)
% 0.99/1.20          | ~ (l1_pre_topc @ X22))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.99/1.20  thf('205', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['203', '204'])).
% 0.99/1.20  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('207', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('208', plain,
% 0.99/1.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('209', plain, ((l1_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('sup-', [status(thm)], ['207', '208'])).
% 0.99/1.20  thf('210', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['201', '202', '209'])).
% 0.99/1.20  thf('211', plain,
% 0.99/1.20      (![X27 : $i, X28 : $i]:
% 0.99/1.20         (~ (l1_struct_0 @ X27)
% 0.99/1.20          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.99/1.20          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.99/1.20          | ~ (l1_struct_0 @ X28))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.99/1.20  thf('212', plain,
% 0.99/1.20      (((~ (l1_struct_0 @ sk_D_2)
% 0.99/1.20         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.99/1.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['210', '211'])).
% 0.99/1.20  thf('213', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('214', plain, ((l1_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('sup-', [status(thm)], ['207', '208'])).
% 0.99/1.20  thf('215', plain,
% 0.99/1.20      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['212', '213', '214'])).
% 0.99/1.20  thf('216', plain,
% 0.99/1.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.99/1.20         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['197', '215'])).
% 0.99/1.20  thf('217', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('218', plain,
% 0.99/1.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['216', '217'])).
% 0.99/1.20  thf('219', plain,
% 0.99/1.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.99/1.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['196', '218'])).
% 0.99/1.20  thf('220', plain, ((l1_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('sup-', [status(thm)], ['207', '208'])).
% 0.99/1.20  thf('221', plain,
% 0.99/1.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('demod', [status(thm)], ['219', '220'])).
% 0.99/1.20  thf('222', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('223', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('224', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.20  thf('225', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_A)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['223', '224'])).
% 0.99/1.20  thf('226', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('227', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('228', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.99/1.20  thf('229', plain,
% 0.99/1.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X29 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X29)
% 0.99/1.20          | ~ (l1_pre_topc @ X30)
% 0.99/1.20          | (v2_struct_0 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X31)
% 0.99/1.20          | ~ (m1_pre_topc @ X31 @ X30)
% 0.99/1.20          | (m1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31) @ X30))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.99/1.20  thf('230', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['228', '229'])).
% 0.99/1.20  thf('231', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('232', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['230', '231'])).
% 0.99/1.20  thf('233', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['232'])).
% 0.99/1.20  thf('234', plain,
% 0.99/1.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['222', '233'])).
% 0.99/1.20  thf('235', plain, (~ (v2_struct_0 @ sk_B)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('236', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.99/1.20      inference('clc', [status(thm)], ['234', '235'])).
% 0.99/1.20  thf('237', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('238', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['236', '237'])).
% 0.99/1.20  thf(d2_tsep_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.99/1.20           ( ![C:$i]:
% 0.99/1.20             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.99/1.20               ( ![D:$i]:
% 0.99/1.20                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.99/1.20                     ( m1_pre_topc @ D @ A ) ) =>
% 0.99/1.20                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.99/1.20                     ( ( u1_struct_0 @ D ) =
% 0.99/1.20                       ( k2_xboole_0 @
% 0.99/1.20                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.99/1.20  thf('239', plain,
% 0.99/1.20      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.99/1.20         ((v2_struct_0 @ X23)
% 0.99/1.20          | ~ (m1_pre_topc @ X23 @ X24)
% 0.99/1.20          | (v2_struct_0 @ X25)
% 0.99/1.20          | ~ (v1_pre_topc @ X25)
% 0.99/1.20          | ~ (m1_pre_topc @ X25 @ X24)
% 0.99/1.20          | ((X25) != (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.99/1.20          | ((u1_struct_0 @ X25)
% 0.99/1.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 0.99/1.20          | ~ (m1_pre_topc @ X26 @ X24)
% 0.99/1.20          | (v2_struct_0 @ X26)
% 0.99/1.20          | ~ (l1_pre_topc @ X24)
% 0.99/1.20          | (v2_struct_0 @ X24))),
% 0.99/1.20      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.99/1.20  thf('240', plain,
% 0.99/1.20      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.99/1.20         ((v2_struct_0 @ X24)
% 0.99/1.20          | ~ (l1_pre_topc @ X24)
% 0.99/1.20          | (v2_struct_0 @ X26)
% 0.99/1.20          | ~ (m1_pre_topc @ X26 @ X24)
% 0.99/1.20          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.99/1.20              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 0.99/1.20          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 0.99/1.20          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.99/1.20          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.99/1.20          | ~ (m1_pre_topc @ X23 @ X24)
% 0.99/1.20          | (v2_struct_0 @ X23))),
% 0.99/1.20      inference('simplify', [status(thm)], ['239'])).
% 0.99/1.20  thf('241', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 0.99/1.20        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['238', '240'])).
% 0.99/1.20  thf('242', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.99/1.20  thf('243', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('244', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('245', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['241', '242', '243', '244'])).
% 0.99/1.20  thf('246', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_B)
% 0.99/1.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20            = (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 0.99/1.20        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['245'])).
% 0.99/1.20  thf('247', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('248', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('249', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['236', '237'])).
% 0.99/1.20  thf('250', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.20  thf('251', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_C_1)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ 
% 0.99/1.20           (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['249', '250'])).
% 0.99/1.20  thf('252', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('253', plain,
% 0.99/1.20      (![X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X7 @ X8)
% 0.99/1.20          | (v2_pre_topc @ X7)
% 0.99/1.20          | ~ (l1_pre_topc @ X8)
% 0.99/1.20          | ~ (v2_pre_topc @ X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.99/1.20  thf('254', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_A)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20        | (v2_pre_topc @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['252', '253'])).
% 0.99/1.20  thf('255', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('256', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('257', plain, ((v2_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['254', '255', '256'])).
% 0.99/1.20  thf('258', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('259', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ 
% 0.99/1.20        (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['251', '257', '258'])).
% 0.99/1.20  thf('260', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('261', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.99/1.20  thf('262', plain,
% 0.99/1.20      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.99/1.20         ((v2_struct_0 @ X34)
% 0.99/1.20          | ~ (m1_pre_topc @ X34 @ X35)
% 0.99/1.20          | (m1_pre_topc @ X34 @ (k1_tsep_1 @ X35 @ X34 @ X36))
% 0.99/1.20          | ~ (m1_pre_topc @ X36 @ X35)
% 0.99/1.20          | (v2_struct_0 @ X36)
% 0.99/1.20          | ~ (l1_pre_topc @ X35)
% 0.99/1.20          | ~ (v2_pre_topc @ X35)
% 0.99/1.20          | (v2_struct_0 @ X35))),
% 0.99/1.20      inference('cnf', [status(esa)], [t22_tsep_1])).
% 0.99/1.20  thf('263', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_C_1)
% 0.99/1.20          | ~ (v2_pre_topc @ sk_C_1)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['261', '262'])).
% 0.99/1.20  thf('264', plain, ((v2_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['254', '255', '256'])).
% 0.99/1.20  thf('265', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('266', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['263', '264', '265'])).
% 0.99/1.20  thf('267', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['266'])).
% 0.99/1.20  thf('268', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['260', '267'])).
% 0.99/1.20  thf('269', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('270', plain,
% 0.99/1.20      (((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | (v2_struct_0 @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['268', '269'])).
% 0.99/1.20  thf('271', plain, (~ (v2_struct_0 @ sk_B)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('272', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['270', '271'])).
% 0.99/1.20  thf('273', plain,
% 0.99/1.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X37 @ X38)
% 0.99/1.20          | ~ (m1_pre_topc @ X37 @ X39)
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.99/1.20          | ~ (m1_pre_topc @ X39 @ X38)
% 0.99/1.20          | ~ (l1_pre_topc @ X38)
% 0.99/1.20          | ~ (v2_pre_topc @ X38))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.99/1.20  thf('274', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['272', '273'])).
% 0.99/1.20  thf('275', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['236', '237'])).
% 0.99/1.20  thf('276', plain,
% 0.99/1.20      (![X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X7 @ X8)
% 0.99/1.20          | (v2_pre_topc @ X7)
% 0.99/1.20          | ~ (l1_pre_topc @ X8)
% 0.99/1.20          | ~ (v2_pre_topc @ X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.99/1.20  thf('277', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_C_1)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['275', '276'])).
% 0.99/1.20  thf('278', plain, ((v2_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['254', '255', '256'])).
% 0.99/1.20  thf('279', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('280', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['277', '278', '279'])).
% 0.99/1.20  thf('281', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['236', '237'])).
% 0.99/1.20  thf('282', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X21 @ X22)
% 0.99/1.20          | (l1_pre_topc @ X21)
% 0.99/1.20          | ~ (l1_pre_topc @ X22))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.99/1.20  thf('283', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['281', '282'])).
% 0.99/1.20  thf('284', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('285', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['283', '284'])).
% 0.99/1.20  thf('286', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.99/1.20      inference('demod', [status(thm)], ['274', '280', '285'])).
% 0.99/1.20  thf('287', plain,
% 0.99/1.20      ((~ (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.99/1.20           (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['259', '286'])).
% 0.99/1.20  thf('288', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['270', '271'])).
% 0.99/1.20  thf('289', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.99/1.20        (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['287', '288'])).
% 0.99/1.20  thf('290', plain,
% 0.99/1.20      (((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.99/1.20         (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))
% 0.99/1.20        | ~ (l1_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup+', [status(thm)], ['248', '289'])).
% 0.99/1.20  thf('291', plain, ((l1_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('sup-', [status(thm)], ['207', '208'])).
% 0.99/1.20  thf('292', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.99/1.20        (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['290', '291'])).
% 0.99/1.20  thf('293', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('294', plain,
% 0.99/1.20      ((~ (r1_tarski @ (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20            = (k2_struct_0 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['292', '293'])).
% 0.99/1.20  thf('295', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20            = (k2_struct_0 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['247', '294'])).
% 0.99/1.20  thf('296', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['270', '271'])).
% 0.99/1.20  thf('297', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('298', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['296', '297'])).
% 0.99/1.20  thf('299', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['283', '284'])).
% 0.99/1.20  thf('300', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('301', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.99/1.20        (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['298', '299', '300'])).
% 0.99/1.20  thf('302', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('303', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20            = (k2_struct_0 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['301', '302'])).
% 0.99/1.20  thf('304', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['236', '237'])).
% 0.99/1.20  thf('305', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('306', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['304', '305'])).
% 0.99/1.20  thf('307', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('308', plain,
% 0.99/1.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.99/1.20         (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('demod', [status(thm)], ['306', '307'])).
% 0.99/1.20  thf('309', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['283', '284'])).
% 0.99/1.20  thf('310', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)) @ 
% 0.99/1.20        (k2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['308', '309'])).
% 0.99/1.20  thf('311', plain,
% 0.99/1.20      (((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20         = (k2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['303', '310'])).
% 0.99/1.20  thf('312', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.99/1.20      inference('simplify', [status(thm)], ['5'])).
% 0.99/1.20  thf('313', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['283', '284'])).
% 0.99/1.20  thf('314', plain,
% 0.99/1.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('315', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['313', '314'])).
% 0.99/1.20  thf('316', plain,
% 0.99/1.20      (((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20         = (k2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['295', '311', '312', '315'])).
% 0.99/1.20  thf('317', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('318', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('319', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.99/1.20  thf('320', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0) @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['232'])).
% 0.99/1.20  thf('321', plain,
% 0.99/1.20      (((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['319', '320'])).
% 0.99/1.20  thf('322', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['321'])).
% 0.99/1.20  thf('323', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('324', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['322', '323'])).
% 0.99/1.20  thf('325', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((m1_pre_topc @ X0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ X1)
% 0.99/1.20          | ~ (l1_pre_topc @ X1)
% 0.99/1.20          | ~ (v2_pre_topc @ X1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.20  thf('326', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_C_1)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ 
% 0.99/1.20           (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['324', '325'])).
% 0.99/1.20  thf('327', plain, ((v2_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['254', '255', '256'])).
% 0.99/1.20  thf('328', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('329', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ 
% 0.99/1.20        (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['326', '327', '328'])).
% 0.99/1.20  thf('330', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.99/1.20  thf('331', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['266'])).
% 0.99/1.20  thf('332', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['330', '331'])).
% 0.99/1.20  thf('333', plain,
% 0.99/1.20      (((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['332'])).
% 0.99/1.20  thf('334', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('335', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('clc', [status(thm)], ['333', '334'])).
% 0.99/1.20  thf('336', plain,
% 0.99/1.20      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X37 @ X38)
% 0.99/1.20          | ~ (m1_pre_topc @ X37 @ X39)
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.99/1.20          | ~ (m1_pre_topc @ X39 @ X38)
% 0.99/1.20          | ~ (l1_pre_topc @ X38)
% 0.99/1.20          | ~ (v2_pre_topc @ X38))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.99/1.20  thf('337', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.99/1.20          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['335', '336'])).
% 0.99/1.20  thf('338', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['322', '323'])).
% 0.99/1.20  thf('339', plain,
% 0.99/1.20      (![X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X7 @ X8)
% 0.99/1.20          | (v2_pre_topc @ X7)
% 0.99/1.20          | ~ (l1_pre_topc @ X8)
% 0.99/1.20          | ~ (v2_pre_topc @ X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.99/1.20  thf('340', plain,
% 0.99/1.20      ((~ (v2_pre_topc @ sk_C_1)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['338', '339'])).
% 0.99/1.20  thf('341', plain, ((v2_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['254', '255', '256'])).
% 0.99/1.20  thf('342', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('343', plain, ((v2_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['340', '341', '342'])).
% 0.99/1.20  thf('344', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['322', '323'])).
% 0.99/1.20  thf('345', plain,
% 0.99/1.20      (![X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X21 @ X22)
% 0.99/1.20          | (l1_pre_topc @ X21)
% 0.99/1.20          | ~ (l1_pre_topc @ X22))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.99/1.20  thf('346', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['344', '345'])).
% 0.99/1.20  thf('347', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('348', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['346', '347'])).
% 0.99/1.20  thf('349', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.99/1.20          | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 0.99/1.20      inference('demod', [status(thm)], ['337', '343', '348'])).
% 0.99/1.20  thf('350', plain,
% 0.99/1.20      ((~ (m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.99/1.20        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.99/1.20           (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['329', '349'])).
% 0.99/1.20  thf('351', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('clc', [status(thm)], ['333', '334'])).
% 0.99/1.20  thf('352', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.99/1.20        (u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['350', '351'])).
% 0.99/1.20  thf('353', plain,
% 0.99/1.20      (((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.99/1.20         (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.99/1.20        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['318', '352'])).
% 0.99/1.20  thf('354', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['346', '347'])).
% 0.99/1.20  thf('355', plain,
% 0.99/1.20      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('356', plain, ((l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['354', '355'])).
% 0.99/1.20  thf('357', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ 
% 0.99/1.20        (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['353', '356'])).
% 0.99/1.20  thf('358', plain,
% 0.99/1.20      ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_C_1)),
% 0.99/1.20      inference('clc', [status(thm)], ['322', '323'])).
% 0.99/1.20  thf('359', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('360', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (r1_tarski @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 0.99/1.20           (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['358', '359'])).
% 0.99/1.20  thf('361', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('362', plain,
% 0.99/1.20      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 0.99/1.20         (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['360', '361'])).
% 0.99/1.20  thf('363', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['346', '347'])).
% 0.99/1.20  thf('364', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)) @ 
% 0.99/1.20        (k2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['362', '363'])).
% 0.99/1.20  thf('365', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('366', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1)
% 0.99/1.20            = (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['364', '365'])).
% 0.99/1.20  thf('367', plain,
% 0.99/1.20      ((m1_pre_topc @ sk_C_1 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('clc', [status(thm)], ['333', '334'])).
% 0.99/1.20  thf('368', plain,
% 0.99/1.20      (![X15 : $i, X16 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X15)
% 0.99/1.20          | ~ (m1_pre_topc @ X15 @ X16)
% 0.99/1.20          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.99/1.20          | ~ (l1_pre_topc @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.99/1.20  thf('369', plain,
% 0.99/1.20      ((~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.99/1.20        | (r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.99/1.20           (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['367', '368'])).
% 0.99/1.20  thf('370', plain, ((l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['346', '347'])).
% 0.99/1.20  thf('371', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('372', plain,
% 0.99/1.20      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ 
% 0.99/1.20        (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['369', '370', '371'])).
% 0.99/1.20  thf('373', plain,
% 0.99/1.20      (((k2_struct_0 @ sk_C_1)
% 0.99/1.20         = (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['366', '372'])).
% 0.99/1.20  thf('374', plain,
% 0.99/1.20      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['357', '373'])).
% 0.99/1.20  thf('375', plain,
% 0.99/1.20      (![X0 : $i, X2 : $i]:
% 0.99/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('376', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_C_1))
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['374', '375'])).
% 0.99/1.20  thf('377', plain,
% 0.99/1.20      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))
% 0.99/1.20        | ~ (l1_struct_0 @ sk_C_1)
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['317', '376'])).
% 0.99/1.20  thf('378', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.99/1.20      inference('simplify', [status(thm)], ['5'])).
% 0.99/1.20  thf('379', plain, ((l1_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('sup-', [status(thm)], ['207', '208'])).
% 0.99/1.20  thf('380', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['377', '378', '379'])).
% 0.99/1.20  thf('381', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['183', '184', '187'])).
% 0.99/1.20  thf('382', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('383', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.99/1.20  thf('384', plain,
% 0.99/1.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X29 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X29)
% 0.99/1.20          | ~ (l1_pre_topc @ X30)
% 0.99/1.20          | (v2_struct_0 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X31)
% 0.99/1.20          | ~ (m1_pre_topc @ X31 @ X30)
% 0.99/1.20          | (v1_pre_topc @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.99/1.20  thf('385', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['383', '384'])).
% 0.99/1.20  thf('386', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('387', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0))
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['385', '386'])).
% 0.99/1.20  thf('388', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_struct_0 @ sk_C_1)
% 0.99/1.20          | (v2_struct_0 @ X0)
% 0.99/1.20          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 0.99/1.20          | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ X0)))),
% 0.99/1.20      inference('simplify', [status(thm)], ['387'])).
% 0.99/1.20  thf('389', plain,
% 0.99/1.20      (((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['382', '388'])).
% 0.99/1.20  thf('390', plain, (~ (v2_struct_0 @ sk_B)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('391', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B)))),
% 0.99/1.20      inference('clc', [status(thm)], ['389', '390'])).
% 0.99/1.20  thf('392', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('393', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))),
% 0.99/1.20      inference('clc', [status(thm)], ['391', '392'])).
% 0.99/1.20  thf('394', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_B)
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1)
% 0.99/1.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.99/1.20        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_C_1 @ sk_B))
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['246', '316', '380', '381', '393'])).
% 0.99/1.20  thf('395', plain,
% 0.99/1.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.20         (~ (m1_pre_topc @ X29 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X29)
% 0.99/1.20          | ~ (l1_pre_topc @ X30)
% 0.99/1.20          | (v2_struct_0 @ X30)
% 0.99/1.20          | (v2_struct_0 @ X31)
% 0.99/1.20          | ~ (m1_pre_topc @ X31 @ X30)
% 0.99/1.20          | ~ (v2_struct_0 @ (k1_tsep_1 @ X30 @ X29 @ X31)))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.99/1.20  thf('396', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1)
% 0.99/1.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1)
% 0.99/1.20        | ~ (l1_pre_topc @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1)
% 0.99/1.20        | ~ (m1_pre_topc @ sk_C_1 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['394', '395'])).
% 0.99/1.20  thf('397', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('398', plain, ((l1_pre_topc @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['205', '206'])).
% 0.99/1.20  thf('399', plain, ((m1_pre_topc @ sk_C_1 @ sk_C_1)),
% 0.99/1.20      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.99/1.20  thf('400', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1)
% 0.99/1.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_B)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1)
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('demod', [status(thm)], ['396', '397', '398', '399'])).
% 0.99/1.20  thf('401', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_B)
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1)
% 0.99/1.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))
% 0.99/1.20        | (v2_struct_0 @ sk_C_1))),
% 0.99/1.20      inference('simplify', [status(thm)], ['400'])).
% 0.99/1.20  thf('402', plain, (~ (v2_struct_0 @ sk_B)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('403', plain,
% 0.99/1.20      (((v2_struct_0 @ sk_C_1)
% 0.99/1.20        | ((k2_struct_0 @ sk_C_1)
% 0.99/1.20            = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))))),
% 0.99/1.20      inference('clc', [status(thm)], ['401', '402'])).
% 0.99/1.20  thf('404', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('405', plain,
% 0.99/1.20      (((k2_struct_0 @ sk_C_1)
% 0.99/1.20         = (k2_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 0.99/1.20      inference('clc', [status(thm)], ['403', '404'])).
% 0.99/1.20  thf(t70_xboole_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.99/1.20            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.99/1.20       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.99/1.20            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.99/1.20  thf('406', plain,
% 0.99/1.20      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.99/1.20         ((r1_xboole_0 @ X3 @ X6)
% 0.99/1.20          | ~ (r1_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X6)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.99/1.20  thf('407', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.99/1.20          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['405', '406'])).
% 0.99/1.20  thf('408', plain,
% 0.99/1.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['221', '407'])).
% 0.99/1.20  thf('409', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('410', plain,
% 0.99/1.20      (![X9 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf('411', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('split', [status(esa)], ['198'])).
% 0.99/1.20  thf('412', plain,
% 0.99/1.20      (![X27 : $i, X28 : $i]:
% 0.99/1.20         (~ (l1_struct_0 @ X27)
% 0.99/1.20          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.99/1.20          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.99/1.20          | ~ (l1_struct_0 @ X28))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.99/1.20  thf('413', plain,
% 0.99/1.20      (((~ (l1_struct_0 @ sk_D_2)
% 0.99/1.20         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.99/1.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['411', '412'])).
% 0.99/1.20  thf('414', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('415', plain, ((l1_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('sup-', [status(thm)], ['207', '208'])).
% 0.99/1.20  thf('416', plain,
% 0.99/1.20      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['413', '414', '415'])).
% 0.99/1.20  thf('417', plain,
% 0.99/1.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.99/1.20         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['410', '416'])).
% 0.99/1.20  thf('418', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('419', plain,
% 0.99/1.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['417', '418'])).
% 0.99/1.20  thf('420', plain,
% 0.99/1.20      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.99/1.20         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('sup+', [status(thm)], ['409', '419'])).
% 0.99/1.20  thf('421', plain, ((l1_struct_0 @ sk_C_1)),
% 0.99/1.20      inference('sup-', [status(thm)], ['207', '208'])).
% 0.99/1.20  thf('422', plain,
% 0.99/1.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['420', '421'])).
% 0.99/1.20  thf('423', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.99/1.20          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['405', '406'])).
% 0.99/1.20  thf('424', plain,
% 0.99/1.20      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.99/1.20         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['422', '423'])).
% 0.99/1.20  thf('425', plain,
% 0.99/1.20      ((~ (r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))
% 0.99/1.20        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.99/1.20      inference('demod', [status(thm)], ['193', '194'])).
% 0.99/1.20  thf('426', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['424', '425'])).
% 0.99/1.20  thf('427', plain,
% 0.99/1.20      (![X32 : $i, X33 : $i]:
% 0.99/1.20         (~ (l1_struct_0 @ X32)
% 0.99/1.20          | ~ (l1_struct_0 @ X33)
% 0.99/1.20          | (r1_tsep_1 @ X33 @ X32)
% 0.99/1.20          | ~ (r1_tsep_1 @ X32 @ X33))),
% 0.99/1.20      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.99/1.20  thf('428', plain,
% 0.99/1.20      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.99/1.20         | ~ (l1_struct_0 @ sk_B)
% 0.99/1.20         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['426', '427'])).
% 0.99/1.20  thf('429', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.20      inference('sup-', [status(thm)], ['185', '186'])).
% 0.99/1.20  thf('430', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('431', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('demod', [status(thm)], ['428', '429', '430'])).
% 0.99/1.20  thf('432', plain,
% 0.99/1.20      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.99/1.20      inference('split', [status(esa)], ['0'])).
% 0.99/1.20  thf('433', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['431', '432'])).
% 0.99/1.20  thf('434', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['424', '425'])).
% 0.99/1.20  thf('435', plain,
% 0.99/1.20      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.99/1.20      inference('split', [status(esa)], ['0'])).
% 0.99/1.20  thf('436', plain,
% 0.99/1.20      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.99/1.20      inference('sup-', [status(thm)], ['434', '435'])).
% 0.99/1.20  thf('437', plain,
% 0.99/1.20      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.99/1.20      inference('split', [status(esa)], ['0'])).
% 0.99/1.20  thf('438', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.99/1.20      inference('split', [status(esa)], ['198'])).
% 0.99/1.20  thf('439', plain, (((r1_tsep_1 @ sk_C_1 @ sk_D_2))),
% 0.99/1.20      inference('sat_resolution*', [status(thm)], ['433', '436', '437', '438'])).
% 0.99/1.20  thf('440', plain,
% 0.99/1.20      ((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))),
% 0.99/1.20      inference('simpl_trail', [status(thm)], ['408', '439'])).
% 0.99/1.20  thf('441', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.99/1.20      inference('demod', [status(thm)], ['195', '440'])).
% 0.99/1.20  thf('442', plain,
% 0.99/1.20      (![X32 : $i, X33 : $i]:
% 0.99/1.20         (~ (l1_struct_0 @ X32)
% 0.99/1.20          | ~ (l1_struct_0 @ X33)
% 0.99/1.20          | (r1_tsep_1 @ X33 @ X32)
% 0.99/1.20          | ~ (r1_tsep_1 @ X32 @ X33))),
% 0.99/1.20      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.99/1.20  thf('443', plain,
% 0.99/1.20      (((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.99/1.20        | ~ (l1_struct_0 @ sk_B)
% 0.99/1.20        | ~ (l1_struct_0 @ sk_D_2))),
% 0.99/1.20      inference('sup-', [status(thm)], ['441', '442'])).
% 0.99/1.20  thf('444', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.20      inference('sup-', [status(thm)], ['185', '186'])).
% 0.99/1.20  thf('445', plain, ((l1_struct_0 @ sk_D_2)),
% 0.99/1.20      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.20  thf('446', plain, ((r1_tsep_1 @ sk_B @ sk_D_2)),
% 0.99/1.20      inference('demod', [status(thm)], ['443', '444', '445'])).
% 0.99/1.20  thf('447', plain, (($false) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.99/1.21      inference('demod', [status(thm)], ['1', '446'])).
% 0.99/1.21  thf('448', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.99/1.21      inference('demod', [status(thm)], ['195', '440'])).
% 0.99/1.21  thf('449', plain,
% 0.99/1.21      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.99/1.21      inference('split', [status(esa)], ['0'])).
% 0.99/1.21  thf('450', plain, (((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.99/1.21      inference('sup-', [status(thm)], ['448', '449'])).
% 0.99/1.21  thf('451', plain,
% 0.99/1.21      (~ ((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.99/1.21      inference('split', [status(esa)], ['0'])).
% 0.99/1.21  thf('452', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.99/1.21      inference('sat_resolution*', [status(thm)], ['450', '451'])).
% 0.99/1.21  thf('453', plain, ($false),
% 0.99/1.21      inference('simpl_trail', [status(thm)], ['447', '452'])).
% 0.99/1.21  
% 0.99/1.21  % SZS output end Refutation
% 0.99/1.21  
% 0.99/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
