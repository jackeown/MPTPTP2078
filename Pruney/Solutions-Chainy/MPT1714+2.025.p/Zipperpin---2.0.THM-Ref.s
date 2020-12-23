%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zb6Ttx8NBE

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 886 expanded)
%              Number of leaves         :   28 ( 265 expanded)
%              Depth                    :   30
%              Number of atoms          : 1058 (11903 expanded)
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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['19'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( r1_tsep_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('22',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('25',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_tsep_1 @ X19 @ X18 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('34',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('37',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('40',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

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

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('49',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('60',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

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

thf('63',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('66',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_tsep_1 @ X19 @ X18 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('70',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('73',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('76',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('78',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['65','80'])).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['64','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('86',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( r1_tsep_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('95',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['62','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['90','91'])).

thf('98',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['61','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('101',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['102'])).

thf('104',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['102'])).

thf('107',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['102'])).

thf('109',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('110',plain,(
    r1_tsep_1 @ sk_D_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['104','107','108','109'])).

thf('111',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['60','110'])).

thf('112',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('113',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['102'])).

thf('115',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('116',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','57'])).

thf('118',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('119',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('122',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['115','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['90','91'])).

thf('125',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['102'])).

thf('127',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['104','107','109','127','108'])).

thf('129',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['114','128'])).

thf('130',plain,
    ( ~ ( l1_struct_0 @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['113','129'])).

thf('131',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('133',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['90','91'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zb6Ttx8NBE
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 230 iterations in 0.127s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.58  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.58  thf(dt_l1_pre_topc, axiom,
% 0.21/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.58  thf('0', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('1', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf(t23_tmap_1, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.58               ( ![D:$i]:
% 0.21/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.58                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.58                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.58                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.58                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58            ( l1_pre_topc @ A ) ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.58              ( ![C:$i]:
% 0.21/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.58                  ( ![D:$i]:
% 0.21/0.58                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.58                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.58                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.58                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.58                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.21/0.58  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t1_tsep_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.58           ( m1_subset_1 @
% 0.21/0.58             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X22 : $i, X23 : $i]:
% 0.21/0.58         (~ (m1_pre_topc @ X22 @ X23)
% 0.21/0.58          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.58          | ~ (l1_pre_topc @ X23))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.58        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.58  thf('5', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_m1_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.58          | (l1_pre_topc @ X16)
% 0.21/0.58          | ~ (l1_pre_topc @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.58  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.58  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('9', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.58  thf(t3_subset, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf(t28_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.58         = (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_C_1 @ sk_D_1) | (r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['19'])).
% 0.21/0.58  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.58       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X20)
% 0.21/0.58          | ~ (l1_struct_0 @ X21)
% 0.21/0.58          | (r1_tsep_1 @ X21 @ X20)
% 0.21/0.58          | ~ (r1_tsep_1 @ X20 @ X21))),
% 0.21/0.58      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((((r1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_tsep_1 @ sk_C_1 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.58  thf('24', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['17', '25'])).
% 0.21/0.58  thf('27', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.58          | (l1_pre_topc @ X16)
% 0.21/0.58          | ~ (l1_pre_topc @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.58  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.58  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('31', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['26', '31'])).
% 0.21/0.58  thf(d3_tsep_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_struct_0 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( l1_struct_0 @ B ) =>
% 0.21/0.58           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.58             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X18)
% 0.21/0.58          | ~ (r1_tsep_1 @ X19 @ X18)
% 0.21/0.58          | (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.21/0.58          | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '34'])).
% 0.21/0.58  thf('36', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['15', '37'])).
% 0.21/0.58  thf('39', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.58  thf(t3_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.58          | ~ (r2_hidden @ X8 @ X9)
% 0.21/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.58          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.58          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['40', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf(d4_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.58       ( ![D:$i]:
% 0.21/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.58          | (r2_hidden @ X4 @ X2)
% 0.21/0.58          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.58         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.58          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.58          | ~ (r2_hidden @ X8 @ X9)
% 0.21/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.58          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.21/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 0.21/0.58          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.58          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['51', '54'])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.58          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          (r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.58           (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['47', '56'])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['14', '57'])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.58         = (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['19'])).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X18)
% 0.21/0.58          | ~ (r1_tsep_1 @ X19 @ X18)
% 0.21/0.58          | (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.21/0.58          | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['67', '70'])).
% 0.21/0.58  thf('72', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.58  thf('74', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.58         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['66', '73'])).
% 0.21/0.58  thf('75', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('76', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.58  thf('77', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.58  thf('78', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.58  thf('79', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.58          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.58  thf('80', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          (r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.58           (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.58  thf('81', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['65', '80'])).
% 0.21/0.58  thf('82', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X18)
% 0.21/0.58          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.21/0.58          | (r1_tsep_1 @ X19 @ X18)
% 0.21/0.58          | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.58  thf('83', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.58  thf('84', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.58         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['64', '83'])).
% 0.21/0.58  thf('85', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('86', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.58  thf('87', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['63', '86'])).
% 0.21/0.58  thf('88', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('89', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.58          | (l1_pre_topc @ X16)
% 0.21/0.58          | ~ (l1_pre_topc @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.58  thf('90', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.58  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.58  thf('93', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['87', '92'])).
% 0.21/0.58  thf('94', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X20)
% 0.21/0.58          | ~ (l1_struct_0 @ X21)
% 0.21/0.58          | (r1_tsep_1 @ X21 @ X20)
% 0.21/0.58          | ~ (r1_tsep_1 @ X20 @ X21))),
% 0.21/0.58      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.58  thf('95', plain,
% 0.21/0.58      ((((r1_tsep_1 @ sk_B @ sk_D_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.58  thf('96', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_tsep_1 @ sk_B @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['62', '95'])).
% 0.21/0.58  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.58  thf('98', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.58  thf('99', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['61', '98'])).
% 0.21/0.58  thf('100', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('101', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_B @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.58  thf('102', plain,
% 0.21/0.58      ((~ (r1_tsep_1 @ sk_B @ sk_D_1) | ~ (r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('103', plain,
% 0.21/0.58      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['102'])).
% 0.21/0.58  thf('104', plain,
% 0.21/0.58      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1)) | ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['101', '103'])).
% 0.21/0.58  thf('105', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['87', '92'])).
% 0.21/0.58  thf('106', plain,
% 0.21/0.58      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.21/0.58      inference('split', [status(esa)], ['102'])).
% 0.21/0.58  thf('107', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.58  thf('108', plain,
% 0.21/0.58      (~ ((r1_tsep_1 @ sk_B @ sk_D_1)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.21/0.58      inference('split', [status(esa)], ['102'])).
% 0.21/0.58  thf('109', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.21/0.58      inference('split', [status(esa)], ['19'])).
% 0.21/0.58  thf('110', plain, (((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['104', '107', '108', '109'])).
% 0.21/0.58  thf('111', plain,
% 0.21/0.58      ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['60', '110'])).
% 0.21/0.58  thf('112', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X18)
% 0.21/0.58          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.21/0.58          | (r1_tsep_1 @ X19 @ X18)
% 0.21/0.58          | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.58  thf('113', plain,
% 0.21/0.58      ((~ (l1_struct_0 @ sk_B)
% 0.21/0.58        | (r1_tsep_1 @ sk_B @ sk_D_1)
% 0.21/0.58        | ~ (l1_struct_0 @ sk_D_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['111', '112'])).
% 0.21/0.58  thf('114', plain,
% 0.21/0.58      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['102'])).
% 0.21/0.58  thf('115', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('116', plain,
% 0.21/0.58      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('117', plain,
% 0.21/0.58      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['14', '57'])).
% 0.21/0.58  thf('118', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X18)
% 0.21/0.58          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.21/0.58          | (r1_tsep_1 @ X19 @ X18)
% 0.21/0.58          | ~ (l1_struct_0 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.58  thf('119', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.58         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.58  thf('120', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.58         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['116', '119'])).
% 0.21/0.58  thf('121', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('122', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['120', '121'])).
% 0.21/0.58  thf('123', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.21/0.58         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['115', '122'])).
% 0.21/0.58  thf('124', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.58  thf('125', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['123', '124'])).
% 0.21/0.58  thf('126', plain,
% 0.21/0.58      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.21/0.58      inference('split', [status(esa)], ['102'])).
% 0.21/0.58  thf('127', plain,
% 0.21/0.58      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.58  thf('128', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)],
% 0.21/0.58                ['104', '107', '109', '127', '108'])).
% 0.21/0.58  thf('129', plain, (~ (r1_tsep_1 @ sk_B @ sk_D_1)),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['114', '128'])).
% 0.21/0.58  thf('130', plain, ((~ (l1_struct_0 @ sk_D_1) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('clc', [status(thm)], ['113', '129'])).
% 0.21/0.58  thf('131', plain, ((~ (l1_pre_topc @ sk_D_1) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '130'])).
% 0.21/0.58  thf('132', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('133', plain, (~ (l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['131', '132'])).
% 0.21/0.58  thf('134', plain, (~ (l1_pre_topc @ sk_B)),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '133'])).
% 0.21/0.58  thf('135', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.58  thf('136', plain, ($false), inference('demod', [status(thm)], ['134', '135'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
