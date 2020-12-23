%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXElm8T5K6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:20 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 967 expanded)
%              Number of leaves         :   30 ( 289 expanded)
%              Depth                    :   28
%              Number of atoms          : 1094 (12647 expanded)
%              Number of equality atoms :    7 (  48 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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

thf('8',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( r1_tsep_1 @ X27 @ X26 )
      | ~ ( r1_tsep_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('11',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( r1_tsep_1 @ X25 @ X24 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ( r1_tarski @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('54',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('62',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','66'])).

thf('68',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ( r1_tsep_1 @ X25 @ X24 )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('72',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( r1_tsep_1 @ X27 @ X26 )
      | ~ ( r1_tsep_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('81',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('83',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('84',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('85',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('88',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('89',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( r1_tsep_1 @ X25 @ X24 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('90',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('93',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('96',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('98',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('100',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ( r1_tsep_1 @ X25 @ X24 )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('102',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['85','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('105',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['84','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('108',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( r1_tsep_1 @ X27 @ X26 )
      | ~ ( r1_tsep_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('110',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['83','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('113',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['82','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('116',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['117'])).

thf('119',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['116','118'])).

thf('120',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('121',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['117'])).

thf('122',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['117'])).

thf('124',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('125',plain,(
    r1_tsep_1 @ sk_D_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['119','122','123','124'])).

thf('126',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['81','125'])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('129',plain,
    ( ~ ( l1_struct_0 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['117'])).

thf('131',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('132',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['117'])).

thf('133',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['119','122','124','133','123'])).

thf('135',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['130','134'])).

thf('136',plain,(
    ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['129','135'])).

thf('137',plain,(
    ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['137','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXElm8T5K6
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 20:46:36 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.46/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.62  % Solved by: fo/fo7.sh
% 0.46/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.62  % done 221 iterations in 0.123s
% 0.46/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.62  % SZS output start Refutation
% 0.46/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.62  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.46/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.62  thf(dt_l1_pre_topc, axiom,
% 0.46/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.62  thf('0', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('1', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('2', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('3', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('4', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('5', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('6', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('7', plain, (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf(t23_tmap_1, conjecture,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.62       ( ![B:$i]:
% 0.46/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.62           ( ![C:$i]:
% 0.46/0.62             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.62               ( ![D:$i]:
% 0.46/0.62                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.46/0.62                   ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.62                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.46/0.62                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.46/0.62                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.62    (~( ![A:$i]:
% 0.46/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.62            ( l1_pre_topc @ A ) ) =>
% 0.46/0.62          ( ![B:$i]:
% 0.46/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.62              ( ![C:$i]:
% 0.46/0.62                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.62                  ( ![D:$i]:
% 0.46/0.62                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.46/0.62                      ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.62                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.46/0.62                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.46/0.62                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.62    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.46/0.62  thf('8', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_C_1 @ sk_D_1) | (r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('9', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('split', [status(esa)], ['8'])).
% 0.46/0.62  thf(symmetry_r1_tsep_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.62       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.46/0.62  thf('10', plain,
% 0.46/0.62      (![X26 : $i, X27 : $i]:
% 0.46/0.62         (~ (l1_struct_0 @ X26)
% 0.46/0.62          | ~ (l1_struct_0 @ X27)
% 0.46/0.62          | (r1_tsep_1 @ X27 @ X26)
% 0.46/0.62          | ~ (r1_tsep_1 @ X26 @ X27))),
% 0.46/0.62      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.46/0.62  thf('11', plain,
% 0.46/0.62      ((((r1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_C_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.62  thf('12', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_C_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_tsep_1 @ sk_C_1 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['7', '11'])).
% 0.46/0.62  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf(dt_m1_pre_topc, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( l1_pre_topc @ A ) =>
% 0.46/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.46/0.62  thf('14', plain,
% 0.46/0.62      (![X22 : $i, X23 : $i]:
% 0.46/0.62         (~ (m1_pre_topc @ X22 @ X23)
% 0.46/0.62          | (l1_pre_topc @ X22)
% 0.46/0.62          | ~ (l1_pre_topc @ X23))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.62  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.62  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.62  thf('18', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['12', '17'])).
% 0.46/0.62  thf('19', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['6', '18'])).
% 0.46/0.62  thf('20', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('21', plain,
% 0.46/0.62      (![X22 : $i, X23 : $i]:
% 0.46/0.62         (~ (m1_pre_topc @ X22 @ X23)
% 0.46/0.62          | (l1_pre_topc @ X22)
% 0.46/0.62          | ~ (l1_pre_topc @ X23))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.62  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.62  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('24', plain, ((l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('25', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['19', '24'])).
% 0.46/0.62  thf(d3_tsep_1, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( l1_struct_0 @ A ) =>
% 0.46/0.62       ( ![B:$i]:
% 0.46/0.62         ( ( l1_struct_0 @ B ) =>
% 0.46/0.62           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.46/0.62             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.46/0.62  thf('26', plain,
% 0.46/0.62      (![X24 : $i, X25 : $i]:
% 0.46/0.62         (~ (l1_struct_0 @ X24)
% 0.46/0.62          | ~ (r1_tsep_1 @ X25 @ X24)
% 0.46/0.62          | (r1_xboole_0 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.46/0.62          | ~ (l1_struct_0 @ X25))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.46/0.62  thf('27', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_C_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.62  thf('28', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_C_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['5', '27'])).
% 0.46/0.62  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.62  thf('30', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.62  thf('31', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_D_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['4', '30'])).
% 0.46/0.62  thf('32', plain, ((l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('33', plain,
% 0.46/0.62      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.62  thf(t3_xboole_0, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.62  thf('34', plain,
% 0.46/0.62      (![X6 : $i, X7 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.62  thf('35', plain,
% 0.46/0.62      (![X6 : $i, X7 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.62  thf('36', plain,
% 0.46/0.62      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.62          | ~ (r2_hidden @ X8 @ X9)
% 0.46/0.62          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.62  thf('37', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X1 @ X0)
% 0.46/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.46/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.62  thf('38', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.62          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.46/0.62          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['34', '37'])).
% 0.46/0.62  thf('39', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.62  thf('40', plain,
% 0.46/0.62      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['33', '39'])).
% 0.46/0.62  thf('41', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf(t1_tsep_1, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( l1_pre_topc @ A ) =>
% 0.46/0.62       ( ![B:$i]:
% 0.46/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.62           ( m1_subset_1 @
% 0.46/0.62             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.62  thf('42', plain,
% 0.46/0.62      (![X28 : $i, X29 : $i]:
% 0.46/0.62         (~ (m1_pre_topc @ X28 @ X29)
% 0.46/0.62          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.46/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.62          | ~ (l1_pre_topc @ X29))),
% 0.46/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.62  thf('43', plain,
% 0.46/0.62      ((~ (l1_pre_topc @ sk_C_1)
% 0.46/0.62        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.46/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.62  thf('44', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.62  thf('45', plain,
% 0.46/0.62      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.62  thf(t3_subset, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.62  thf('46', plain,
% 0.46/0.62      (![X18 : $i, X19 : $i]:
% 0.46/0.62         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.62  thf('47', plain,
% 0.46/0.62      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.62  thf(d10_xboole_0, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.62  thf('48', plain,
% 0.46/0.62      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.46/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.62  thf('49', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.46/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.62  thf(t8_xboole_1, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.62       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.62  thf('50', plain,
% 0.46/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.62         (~ (r1_tarski @ X15 @ X16)
% 0.46/0.62          | ~ (r1_tarski @ X17 @ X16)
% 0.46/0.62          | (r1_tarski @ (k2_xboole_0 @ X15 @ X17) @ X16))),
% 0.46/0.62      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.46/0.62  thf('51', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.46/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.62  thf('52', plain,
% 0.46/0.62      ((r1_tarski @ 
% 0.46/0.62        (k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)) @ 
% 0.46/0.62        (u1_struct_0 @ sk_C_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['47', '51'])).
% 0.46/0.62  thf(t7_xboole_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.62  thf('53', plain,
% 0.46/0.62      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.46/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.62  thf('54', plain,
% 0.46/0.62      (![X10 : $i, X12 : $i]:
% 0.46/0.62         (((X10) = (X12))
% 0.46/0.62          | ~ (r1_tarski @ X12 @ X10)
% 0.46/0.62          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.62  thf('55', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.62          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.62  thf('56', plain,
% 0.46/0.62      (((k2_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))
% 0.46/0.62         = (u1_struct_0 @ sk_C_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.46/0.62  thf('57', plain,
% 0.46/0.62      (![X6 : $i, X7 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.62  thf(d3_xboole_0, axiom,
% 0.46/0.62    (![A:$i,B:$i,C:$i]:
% 0.46/0.62     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.46/0.62       ( ![D:$i]:
% 0.46/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.62           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.62  thf('58', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.62          | (r2_hidden @ X0 @ X2)
% 0.46/0.62          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.62  thf('59', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.46/0.62         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.62      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.62  thf('60', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X1 @ X0)
% 0.46/0.62          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['57', '59'])).
% 0.46/0.62  thf('61', plain,
% 0.46/0.62      (![X6 : $i, X7 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.62  thf('62', plain,
% 0.46/0.62      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.46/0.62         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.62          | ~ (r2_hidden @ X8 @ X9)
% 0.46/0.62          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.62  thf('63', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.62          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.46/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.62  thf('64', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X2 @ X0)
% 0.46/0.62          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.46/0.62          | (r1_xboole_0 @ X2 @ X0))),
% 0.46/0.62      inference('sup-', [status(thm)], ['60', '63'])).
% 0.46/0.62  thf('65', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.62         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.46/0.62          | (r1_xboole_0 @ X2 @ X0))),
% 0.46/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.62  thf('66', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.46/0.62          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['56', '65'])).
% 0.46/0.62  thf('67', plain,
% 0.46/0.62      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['40', '66'])).
% 0.46/0.62  thf('68', plain,
% 0.46/0.62      (![X24 : $i, X25 : $i]:
% 0.46/0.62         (~ (l1_struct_0 @ X24)
% 0.46/0.62          | ~ (r1_xboole_0 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.46/0.62          | (r1_tsep_1 @ X25 @ X24)
% 0.46/0.62          | ~ (l1_struct_0 @ X25))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.46/0.62  thf('69', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.62  thf('70', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_D_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_B)
% 0.46/0.62         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['3', '69'])).
% 0.46/0.62  thf('71', plain, ((l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('72', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.62  thf('73', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['2', '72'])).
% 0.46/0.62  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('75', plain,
% 0.46/0.62      (![X22 : $i, X23 : $i]:
% 0.46/0.62         (~ (m1_pre_topc @ X22 @ X23)
% 0.46/0.62          | (l1_pre_topc @ X22)
% 0.46/0.62          | ~ (l1_pre_topc @ X23))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.62  thf('76', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.46/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.62  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.62  thf('79', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['73', '78'])).
% 0.46/0.62  thf('80', plain,
% 0.46/0.62      (![X26 : $i, X27 : $i]:
% 0.46/0.62         (~ (l1_struct_0 @ X26)
% 0.46/0.62          | ~ (l1_struct_0 @ X27)
% 0.46/0.62          | (r1_tsep_1 @ X27 @ X26)
% 0.46/0.62          | ~ (r1_tsep_1 @ X26 @ X27))),
% 0.46/0.62      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.46/0.62  thf('81', plain,
% 0.46/0.62      ((((r1_tsep_1 @ sk_B @ sk_D_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_B)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.62  thf('82', plain,
% 0.46/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('83', plain,
% 0.46/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('84', plain,
% 0.46/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('85', plain,
% 0.46/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('86', plain,
% 0.46/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('87', plain,
% 0.46/0.62      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.62  thf('88', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('split', [status(esa)], ['8'])).
% 0.46/0.62  thf('89', plain,
% 0.46/0.62      (![X24 : $i, X25 : $i]:
% 0.46/0.62         (~ (l1_struct_0 @ X24)
% 0.46/0.62          | ~ (r1_tsep_1 @ X25 @ X24)
% 0.46/0.62          | (r1_xboole_0 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.46/0.62          | ~ (l1_struct_0 @ X25))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.46/0.62  thf('90', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_C_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.62  thf('91', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_C_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['87', '90'])).
% 0.46/0.62  thf('92', plain, ((l1_pre_topc @ sk_C_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.62  thf('93', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.62  thf('94', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_D_1)
% 0.46/0.62         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['86', '93'])).
% 0.46/0.62  thf('95', plain, ((l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('96', plain,
% 0.46/0.62      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['94', '95'])).
% 0.46/0.62  thf('97', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.62  thf('98', plain,
% 0.46/0.62      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['96', '97'])).
% 0.46/0.62  thf('99', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.46/0.62          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['56', '65'])).
% 0.46/0.62  thf('100', plain,
% 0.46/0.62      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.62  thf('101', plain,
% 0.46/0.62      (![X24 : $i, X25 : $i]:
% 0.46/0.62         (~ (l1_struct_0 @ X24)
% 0.46/0.62          | ~ (r1_xboole_0 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.46/0.62          | (r1_tsep_1 @ X25 @ X24)
% 0.46/0.62          | ~ (l1_struct_0 @ X25))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.46/0.62  thf('102', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.62  thf('103', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_D_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_B)
% 0.46/0.62         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['85', '102'])).
% 0.46/0.62  thf('104', plain, ((l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('105', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['103', '104'])).
% 0.46/0.62  thf('106', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['84', '105'])).
% 0.46/0.62  thf('107', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.62  thf('108', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.62  thf('109', plain,
% 0.46/0.62      (![X26 : $i, X27 : $i]:
% 0.46/0.62         (~ (l1_struct_0 @ X26)
% 0.46/0.62          | ~ (l1_struct_0 @ X27)
% 0.46/0.62          | (r1_tsep_1 @ X27 @ X26)
% 0.46/0.62          | ~ (r1_tsep_1 @ X26 @ X27))),
% 0.46/0.62      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.46/0.62  thf('110', plain,
% 0.46/0.62      ((((r1_tsep_1 @ sk_B @ sk_D_1)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_B)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.62  thf('111', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_B)
% 0.46/0.62         | ~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62         | (r1_tsep_1 @ sk_B @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['83', '110'])).
% 0.46/0.62  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.62  thf('113', plain,
% 0.46/0.62      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['111', '112'])).
% 0.46/0.62  thf('114', plain,
% 0.46/0.62      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.46/0.62         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['82', '113'])).
% 0.46/0.62  thf('115', plain, ((l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('116', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_B @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['114', '115'])).
% 0.46/0.62  thf('117', plain,
% 0.46/0.62      ((~ (r1_tsep_1 @ sk_B @ sk_D_1) | ~ (r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('118', plain,
% 0.46/0.62      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.46/0.62      inference('split', [status(esa)], ['117'])).
% 0.46/0.62  thf('119', plain,
% 0.46/0.62      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1)) | ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['116', '118'])).
% 0.46/0.62  thf('120', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.62  thf('121', plain,
% 0.46/0.62      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.46/0.62      inference('split', [status(esa)], ['117'])).
% 0.46/0.62  thf('122', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['120', '121'])).
% 0.46/0.62  thf('123', plain,
% 0.46/0.62      (~ ((r1_tsep_1 @ sk_B @ sk_D_1)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.46/0.62      inference('split', [status(esa)], ['117'])).
% 0.46/0.62  thf('124', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.46/0.62      inference('split', [status(esa)], ['8'])).
% 0.46/0.62  thf('125', plain, (((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.46/0.62      inference('sat_resolution*', [status(thm)], ['119', '122', '123', '124'])).
% 0.46/0.62  thf('126', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_B @ sk_D_1)
% 0.46/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.62        | ~ (l1_struct_0 @ sk_D_1))),
% 0.46/0.62      inference('simpl_trail', [status(thm)], ['81', '125'])).
% 0.46/0.62  thf('127', plain,
% 0.46/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.62        | ~ (l1_struct_0 @ sk_D_1)
% 0.46/0.62        | (r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['1', '126'])).
% 0.46/0.62  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.62  thf('129', plain, ((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.46/0.62      inference('demod', [status(thm)], ['127', '128'])).
% 0.46/0.62  thf('130', plain,
% 0.46/0.62      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.46/0.62      inference('split', [status(esa)], ['117'])).
% 0.46/0.62  thf('131', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['73', '78'])).
% 0.46/0.62  thf('132', plain,
% 0.46/0.62      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.46/0.62      inference('split', [status(esa)], ['117'])).
% 0.46/0.62  thf('133', plain,
% 0.46/0.62      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.46/0.62      inference('sup-', [status(thm)], ['131', '132'])).
% 0.46/0.62  thf('134', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.46/0.62      inference('sat_resolution*', [status(thm)],
% 0.46/0.62                ['119', '122', '124', '133', '123'])).
% 0.46/0.62  thf('135', plain, (~ (r1_tsep_1 @ sk_B @ sk_D_1)),
% 0.46/0.62      inference('simpl_trail', [status(thm)], ['130', '134'])).
% 0.46/0.62  thf('136', plain, (~ (l1_struct_0 @ sk_D_1)),
% 0.46/0.62      inference('clc', [status(thm)], ['129', '135'])).
% 0.46/0.62  thf('137', plain, (~ (l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('sup-', [status(thm)], ['0', '136'])).
% 0.46/0.62  thf('138', plain, ((l1_pre_topc @ sk_D_1)),
% 0.46/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.62  thf('139', plain, ($false), inference('demod', [status(thm)], ['137', '138'])).
% 0.46/0.62  
% 0.46/0.62  % SZS output end Refutation
% 0.46/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
