%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ny6n3RszuO

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 568 expanded)
%              Number of leaves         :   30 ( 177 expanded)
%              Depth                    :   29
%              Number of atoms          :  972 (7589 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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

thf('4',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ~ ( r1_tsep_1 @ X16 @ X15 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('20',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('30',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      = k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('37',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ( r1_tsep_1 @ X16 @ X15 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('41',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('51',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( r1_tsep_1 @ X18 @ X17 )
      | ~ ( r1_tsep_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('53',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_D @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('56',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_D @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( r1_tsep_1 @ sk_D @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('59',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tsep_1 @ sk_B_1 @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B_1 )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('66',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( r1_tsep_1 @ X18 @ X17 )
      | ~ ( r1_tsep_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('72',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_D @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('75',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_D @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_tsep_1 @ sk_D @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('78',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ~ ( r1_tsep_1 @ X16 @ X15 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('80',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('86',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('88',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      = k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','92'])).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ( r1_tsep_1 @ X16 @ X15 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('95',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('98',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('101',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['60'])).

thf('103',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('105',plain,
    ( ~ ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['60'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B_1 )
    | ~ ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['60'])).

thf('108',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('110',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('111',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( r1_tsep_1 @ X18 @ X17 )
      | ~ ( r1_tsep_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('112',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_D @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('115',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_D @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( r1_tsep_1 @ sk_D @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('118',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B_1 )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference(split,[status(esa)],['60'])).

thf('120',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('122',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['62','103','106','107','120','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ny6n3RszuO
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 99 iterations in 0.036s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(dt_l1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.50  thf('0', plain, (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('1', plain, (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('2', plain, (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('3', plain, (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf(t23_tmap_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                   ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.50                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.50                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.50                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50                  ( ![D:$i]:
% 0.22/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                      ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.50                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.50                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.50                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.22/0.50  thf('4', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t1_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( m1_subset_1 @
% 0.22/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.50          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.50          | ~ (l1_pre_topc @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_m1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X13 @ X14)
% 0.22/0.50          | (l1_pre_topc @ X13)
% 0.22/0.50          | ~ (l1_pre_topc @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '11'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_D @ sk_C_1)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['17'])).
% 0.22/0.50  thf(d3_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_struct_0 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( l1_struct_0 @ B ) =>
% 0.22/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.22/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X15)
% 0.22/0.50          | ~ (r1_tsep_1 @ X16 @ X15)
% 0.22/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.22/0.50          | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_C_1)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '20'])).
% 0.22/0.50  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X13 @ X14)
% 0.22/0.50          | (l1_pre_topc @ X13)
% 0.22/0.50          | ~ (l1_pre_topc @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_C_1)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '27'])).
% 0.22/0.50  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf(t7_xboole_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.50  thf(t4_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.22/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((((k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50          = (k1_xboole_0)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['30', '33'])).
% 0.22/0.50  thf(t77_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.50          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X6 @ X7)
% 0.22/0.50          | ~ (r1_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.22/0.50          | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.22/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50           | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.50  thf('37', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50           | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X15)
% 0.22/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.22/0.50          | (r1_tsep_1 @ X16 @ X15)
% 0.22/0.50          | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_B_1)
% 0.22/0.50         | (r1_tsep_1 @ sk_B_1 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_B_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tsep_1 @ sk_B_1 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '41'])).
% 0.22/0.50  thf('43', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X13 @ X14)
% 0.22/0.50          | (l1_pre_topc @ X13)
% 0.22/0.50          | ~ (l1_pre_topc @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('45', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain, ((l1_pre_topc @ sk_B_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '48'])).
% 0.22/0.50  thf('50', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.22/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X17)
% 0.22/0.50          | ~ (l1_struct_0 @ X18)
% 0.22/0.50          | (r1_tsep_1 @ X18 @ X17)
% 0.22/0.50          | ~ (r1_tsep_1 @ X17 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      ((((r1_tsep_1 @ sk_D @ sk_B_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_B_1)
% 0.22/0.50         | (r1_tsep_1 @ sk_D @ sk_B_1))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '53'])).
% 0.22/0.50  thf('55', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_B_1) | (r1_tsep_1 @ sk_D @ sk_B_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_B_1) | (r1_tsep_1 @ sk_D @ sk_B_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '56'])).
% 0.22/0.50  thf('58', plain, ((l1_pre_topc @ sk_B_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_D @ sk_B_1)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      ((~ (r1_tsep_1 @ sk_B_1 @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B_1)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['60'])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_C_1)) | ((r1_tsep_1 @ sk_D @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['59', '61'])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['17'])).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X17)
% 0.22/0.50          | ~ (l1_struct_0 @ X18)
% 0.22/0.50          | (r1_tsep_1 @ X18 @ X17)
% 0.22/0.50          | ~ (r1_tsep_1 @ X17 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      ((((r1_tsep_1 @ sk_D @ sk_C_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_C_1)
% 0.22/0.50         | (r1_tsep_1 @ sk_D @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['69', '72'])).
% 0.22/0.50  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_C_1) | (r1_tsep_1 @ sk_D @ sk_C_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_C_1) | (r1_tsep_1 @ sk_D @ sk_C_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['68', '75'])).
% 0.22/0.50  thf('77', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_D @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.50  thf('79', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X15)
% 0.22/0.50          | ~ (r1_tsep_1 @ X16 @ X15)
% 0.22/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.22/0.50          | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.50  thf('81', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_C_1)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['67', '80'])).
% 0.22/0.50  thf('82', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('83', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_C_1)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.50  thf('84', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['66', '83'])).
% 0.22/0.50  thf('85', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('86', plain,
% 0.22/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['84', '85'])).
% 0.22/0.50  thf('87', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf('88', plain,
% 0.22/0.50      ((((k3_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50          = (k1_xboole_0)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.50  thf('89', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X6 @ X7)
% 0.22/0.50          | ~ (r1_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.22/0.50          | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.22/0.50  thf('90', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.22/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50           | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['88', '89'])).
% 0.22/0.50  thf('91', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.50  thf('92', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50           | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.50  thf('93', plain,
% 0.22/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['65', '92'])).
% 0.22/0.50  thf('94', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X15)
% 0.22/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.22/0.50          | (r1_tsep_1 @ X16 @ X15)
% 0.22/0.50          | ~ (l1_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.50  thf('95', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_B_1)
% 0.22/0.50         | (r1_tsep_1 @ sk_B_1 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.50  thf('96', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_B_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tsep_1 @ sk_B_1 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['64', '95'])).
% 0.22/0.50  thf('97', plain, ((l1_pre_topc @ sk_B_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('98', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['96', '97'])).
% 0.22/0.50  thf('99', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['63', '98'])).
% 0.22/0.50  thf('100', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('101', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.50  thf('102', plain,
% 0.22/0.50      ((~ (r1_tsep_1 @ sk_B_1 @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B_1 @ sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['60'])).
% 0.22/0.50  thf('103', plain,
% 0.22/0.50      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D)) | ((r1_tsep_1 @ sk_B_1 @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.50  thf('104', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf('105', plain,
% 0.22/0.50      ((~ (r1_tsep_1 @ sk_B_1 @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B_1 @ sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['60'])).
% 0.22/0.50  thf('106', plain,
% 0.22/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_C_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['104', '105'])).
% 0.22/0.50  thf('107', plain,
% 0.22/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_B_1)) | ~ ((r1_tsep_1 @ sk_B_1 @ sk_D))),
% 0.22/0.50      inference('split', [status(esa)], ['60'])).
% 0.22/0.50  thf('108', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('109', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('110', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.50  thf('111', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X17)
% 0.22/0.50          | ~ (l1_struct_0 @ X18)
% 0.22/0.50          | (r1_tsep_1 @ X18 @ X17)
% 0.22/0.50          | ~ (r1_tsep_1 @ X17 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.50  thf('112', plain,
% 0.22/0.50      ((((r1_tsep_1 @ sk_D @ sk_B_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['110', '111'])).
% 0.22/0.50  thf('113', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_B_1)
% 0.22/0.50         | (r1_tsep_1 @ sk_D @ sk_B_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['109', '112'])).
% 0.22/0.50  thf('114', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('115', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_B_1) | (r1_tsep_1 @ sk_D @ sk_B_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['113', '114'])).
% 0.22/0.50  thf('116', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_B_1) | (r1_tsep_1 @ sk_D @ sk_B_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['108', '115'])).
% 0.22/0.50  thf('117', plain, ((l1_pre_topc @ sk_B_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('118', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_D @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.50      inference('demod', [status(thm)], ['116', '117'])).
% 0.22/0.50  thf('119', plain,
% 0.22/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B_1)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['60'])).
% 0.22/0.50  thf('120', plain,
% 0.22/0.50      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['118', '119'])).
% 0.22/0.50  thf('121', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.22/0.50      inference('split', [status(esa)], ['17'])).
% 0.22/0.50  thf('122', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)],
% 0.22/0.50                ['62', '103', '106', '107', '120', '121'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
