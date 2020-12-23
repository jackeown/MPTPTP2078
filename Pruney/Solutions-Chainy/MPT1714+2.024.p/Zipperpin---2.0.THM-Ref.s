%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.moYJ93wl0w

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 876 expanded)
%              Number of leaves         :   28 ( 262 expanded)
%              Depth                    :   29
%              Number of atoms          : 1100 (11754 expanded)
%              Number of equality atoms :    6 (  30 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

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

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( r1_tsep_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('9',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_tsep_1 @ X19 @ X18 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('25',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('43',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_tsep_1 @ X19 @ X18 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('65',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('68',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('71',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('73',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('79',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('86',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('89',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['59','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( r1_tsep_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('98',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['58','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('101',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['57','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['90','95'])).

thf('109',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['105'])).

thf('110',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['105'])).

thf('112',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('113',plain,(
    r1_tsep_1 @ sk_D_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['107','110','111','112'])).

thf('114',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['56','113'])).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('116',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['105'])).

thf('118',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('120',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('122',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('124',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('127',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['118','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('130',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['105'])).

thf('132',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['107','110','112','132','111'])).

thf('134',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['117','133'])).

thf('135',plain,
    ( ~ ( l1_struct_0 @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['116','134'])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('138',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['139','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.moYJ93wl0w
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 193 iterations in 0.094s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.55  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.55  thf(dt_l1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.55  thf('0', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('1', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('2', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('3', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('4', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('5', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf(t23_tmap_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                   ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.55                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.55                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.55                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55                  ( ![D:$i]:
% 0.20/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                      ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.55                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.55                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.55                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_C_1 @ sk_D_1) | (r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.55       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (l1_struct_0 @ X20)
% 0.20/0.55          | ~ (l1_struct_0 @ X21)
% 0.20/0.55          | (r1_tsep_1 @ X21 @ X20)
% 0.20/0.55          | ~ (r1_tsep_1 @ X20 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((((r1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_C_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_tsep_1 @ sk_C_1 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.55  thf('11', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_m1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.55          | (l1_pre_topc @ X16)
% 0.20/0.55          | ~ (l1_pre_topc @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.55  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '16'])).
% 0.20/0.55  thf('18', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.55          | (l1_pre_topc @ X16)
% 0.20/0.55          | ~ (l1_pre_topc @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.55  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('22', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.55  thf(d3_tsep_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( l1_struct_0 @ B ) =>
% 0.20/0.55           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.55             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (l1_struct_0 @ X18)
% 0.20/0.55          | ~ (r1_tsep_1 @ X19 @ X18)
% 0.20/0.55          | (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.20/0.55          | ~ (l1_struct_0 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_C_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '25'])).
% 0.20/0.55  thf('27', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_D_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '28'])).
% 0.20/0.55  thf('30', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf(t3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.55          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.55          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.55          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.55          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '37'])).
% 0.20/0.55  thf('39', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t1_tsep_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( m1_subset_1 @
% 0.20/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.55          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.55          | ~ (l1_pre_topc @ X23))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf(t3_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf(t12_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55         = (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf(d3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X3)
% 0.20/0.55          | (r2_hidden @ X0 @ X2)
% 0.20/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.20/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '50'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X1 @ X2)
% 0.20/0.55          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.55          | (r1_xboole_0 @ X1 @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.55          | (r1_xboole_0 @ X1 @ X2))),
% 0.20/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '54'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['38', '55'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (l1_struct_0 @ X18)
% 0.20/0.55          | ~ (r1_tsep_1 @ X19 @ X18)
% 0.20/0.55          | (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.20/0.55          | ~ (l1_struct_0 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_C_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.55  thf('67', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_D_1)
% 0.20/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['61', '68'])).
% 0.20/0.55  thf('70', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55         = (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.20/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.55          | ~ (r2_hidden @ X8 @ X9)
% 0.20/0.55          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.55          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X2 @ X1)
% 0.20/0.55          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.55          | (r1_xboole_0 @ X2 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['77', '80'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.55          | (r1_xboole_0 @ X2 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['74', '82'])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['73', '83'])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (l1_struct_0 @ X18)
% 0.20/0.55          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.20/0.55          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.55          | ~ (l1_struct_0 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_D_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.55         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['60', '86'])).
% 0.20/0.55  thf('88', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['59', '89'])).
% 0.20/0.55  thf('91', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.55          | (l1_pre_topc @ X16)
% 0.20/0.55          | ~ (l1_pre_topc @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.55  thf('93', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.55  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['90', '95'])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (l1_struct_0 @ X20)
% 0.20/0.55          | ~ (l1_struct_0 @ X21)
% 0.20/0.55          | (r1_tsep_1 @ X21 @ X20)
% 0.20/0.55          | ~ (r1_tsep_1 @ X20 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      ((((r1_tsep_1 @ sk_B @ sk_D_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_tsep_1 @ sk_B @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['58', '98'])).
% 0.20/0.55  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['99', '100'])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '101'])).
% 0.20/0.55  thf('103', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_B @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['102', '103'])).
% 0.20/0.55  thf('105', plain,
% 0.20/0.55      ((~ (r1_tsep_1 @ sk_B @ sk_D_1) | ~ (r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('106', plain,
% 0.20/0.55      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['105'])).
% 0.20/0.55  thf('107', plain,
% 0.20/0.55      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1)) | ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['104', '106'])).
% 0.20/0.55  thf('108', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['90', '95'])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['105'])).
% 0.20/0.55  thf('110', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      (~ ((r1_tsep_1 @ sk_B @ sk_D_1)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.20/0.55      inference('split', [status(esa)], ['105'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.20/0.55      inference('split', [status(esa)], ['6'])).
% 0.20/0.55  thf('113', plain, (((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['107', '110', '111', '112'])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['56', '113'])).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (l1_struct_0 @ X18)
% 0.20/0.55          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.20/0.55          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.55          | ~ (l1_struct_0 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.55  thf('116', plain,
% 0.20/0.55      ((~ (l1_struct_0 @ sk_B)
% 0.20/0.55        | (r1_tsep_1 @ sk_B @ sk_D_1)
% 0.20/0.55        | ~ (l1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.55  thf('117', plain,
% 0.20/0.55      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['105'])).
% 0.20/0.55  thf('118', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('119', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('120', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '37'])).
% 0.20/0.55  thf('121', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['74', '82'])).
% 0.20/0.55  thf('122', plain,
% 0.20/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['120', '121'])).
% 0.20/0.55  thf('123', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (l1_struct_0 @ X18)
% 0.20/0.55          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.20/0.55          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.55          | ~ (l1_struct_0 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.55  thf('124', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_D_1)
% 0.20/0.55         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.55  thf('125', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_D_1)
% 0.20/0.55         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.55         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['119', '124'])).
% 0.20/0.55  thf('126', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('127', plain,
% 0.20/0.55      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['125', '126'])).
% 0.20/0.55  thf('128', plain,
% 0.20/0.55      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.20/0.55         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['118', '127'])).
% 0.20/0.55  thf('129', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('130', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['128', '129'])).
% 0.20/0.55  thf('131', plain,
% 0.20/0.55      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['105'])).
% 0.20/0.55  thf('132', plain,
% 0.20/0.55      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['130', '131'])).
% 0.20/0.56  thf('133', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)],
% 0.20/0.56                ['107', '110', '112', '132', '111'])).
% 0.20/0.56  thf('134', plain, (~ (r1_tsep_1 @ sk_B @ sk_D_1)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['117', '133'])).
% 0.20/0.56  thf('135', plain, ((~ (l1_struct_0 @ sk_D_1) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['116', '134'])).
% 0.20/0.56  thf('136', plain, ((~ (l1_pre_topc @ sk_D_1) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '135'])).
% 0.20/0.56  thf('137', plain, ((l1_pre_topc @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.56  thf('138', plain, (~ (l1_struct_0 @ sk_B)),
% 0.20/0.56      inference('demod', [status(thm)], ['136', '137'])).
% 0.20/0.56  thf('139', plain, (~ (l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '138'])).
% 0.20/0.56  thf('140', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.56  thf('141', plain, ($false), inference('demod', [status(thm)], ['139', '140'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
