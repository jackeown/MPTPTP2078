%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQ6l0qqypV

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:16 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 272 expanded)
%              Number of leaves         :   33 (  93 expanded)
%              Depth                    :   32
%              Number of atoms          :  738 (2518 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t22_tmap_1,conjecture,(
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
             => ( ( m1_pre_topc @ B @ C )
               => ( ~ ( r1_tsep_1 @ B @ C )
                  & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) )).

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
               => ( ( m1_pre_topc @ B @ C )
                 => ( ~ ( r1_tsep_1 @ B @ C )
                    & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tmap_1])).

thf('5',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( r1_tsep_1 @ X30 @ X29 )
      | ~ ( r1_tsep_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('8',plain,
    ( ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('24',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('28',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('36',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('47',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,
    ( ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X6 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('62',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','64'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('72',plain,(
    ~ ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('74',plain,(
    r1_tsep_1 @ sk_C @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['24','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('78',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('81',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('83',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('85',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('87',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('91',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQ6l0qqypV
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:33 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 196 iterations in 0.091s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.55  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('0', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('1', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('2', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('3', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('4', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf(t22_tmap_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55               ( ( m1_pre_topc @ B @ C ) =>
% 0.36/0.55                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55                  ( ( m1_pre_topc @ B @ C ) =>
% 0.36/0.55                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_B_1 @ sk_C) | (r1_tsep_1 @ sk_C @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_C @ sk_B_1)) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf(symmetry_r1_tsep_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.55       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X29 : $i, X30 : $i]:
% 0.36/0.55         (~ (l1_struct_0 @ X29)
% 0.36/0.55          | ~ (l1_struct_0 @ X30)
% 0.36/0.55          | (r1_tsep_1 @ X30 @ X29)
% 0.36/0.55          | ~ (r1_tsep_1 @ X29 @ X30))),
% 0.36/0.55      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      ((((r1_tsep_1 @ sk_B_1 @ sk_C)
% 0.36/0.55         | ~ (l1_struct_0 @ sk_B_1)
% 0.36/0.55         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (((~ (l1_pre_topc @ sk_B_1)
% 0.36/0.55         | ~ (l1_struct_0 @ sk_C)
% 0.36/0.55         | (r1_tsep_1 @ sk_B_1 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '8'])).
% 0.36/0.55  thf('10', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_m1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X24 : $i, X25 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X24 @ X25)
% 0.36/0.55          | (l1_pre_topc @ X24)
% 0.36/0.55          | ~ (l1_pre_topc @ X25))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_B_1 @ sk_C)))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_B_1 @ sk_C)))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '15'])).
% 0.36/0.55  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X24 : $i, X25 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X24 @ X25)
% 0.36/0.55          | (l1_pre_topc @ X24)
% 0.36/0.55          | ~ (l1_pre_topc @ X25))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('19', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_B_1 @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.36/0.55      inference('demod', [status(thm)], ['16', '21'])).
% 0.36/0.55  thf(d3_tsep_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_struct_0 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( l1_struct_0 @ B ) =>
% 0.36/0.55           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.36/0.55             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i]:
% 0.36/0.55         (~ (l1_struct_0 @ X27)
% 0.36/0.55          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.36/0.55          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (l1_struct_0 @ X28))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (((~ (l1_struct_0 @ sk_B_1)
% 0.36/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))
% 0.36/0.55         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_B_1 @ sk_C)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i]:
% 0.36/0.55         (~ (l1_struct_0 @ X27)
% 0.36/0.55          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.36/0.55          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (l1_struct_0 @ X28))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (((~ (l1_struct_0 @ sk_B_1)
% 0.36/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))
% 0.36/0.55         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (((~ (l1_pre_topc @ sk_B_1)
% 0.36/0.55         | ~ (l1_struct_0 @ sk_C)
% 0.36/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['27', '30'])).
% 0.36/0.55  thf('32', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (((~ (l1_struct_0 @ sk_C)
% 0.36/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (((~ (l1_pre_topc @ sk_C)
% 0.36/0.55         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '33'])).
% 0.36/0.55  thf('35', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.55  thf('37', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf(t12_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.55  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf(t73_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.36/0.55       ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         ((r1_tarski @ X15 @ X16)
% 0.36/0.55          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.36/0.55          | ~ (r1_xboole_0 @ X15 @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X1 @ X0)
% 0.36/0.55          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.36/0.55          | (r1_tarski @ X1 @ k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      ((((r1_tarski @ (u1_struct_0 @ sk_B_1) @ k1_xboole_0)
% 0.36/0.55         | ~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['36', '41'])).
% 0.36/0.55  thf('43', plain, ((m1_pre_topc @ sk_B_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t1_tsep_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.55           ( m1_subset_1 @
% 0.36/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (![X31 : $i, X32 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X31 @ X32)
% 0.36/0.55          | (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.36/0.55          | ~ (l1_pre_topc @ X32))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_C)
% 0.36/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.55  thf('46', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]:
% 0.36/0.55         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (((r1_tarski @ (u1_struct_0 @ sk_B_1) @ k1_xboole_0))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['42', '49'])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      ((((k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ k1_xboole_0) = (k1_xboole_0)))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf(d1_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf(d3_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X3 @ X6)
% 0.36/0.55          | (r2_hidden @ X3 @ X5)
% 0.36/0.55          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.36/0.55         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X6))),
% 0.36/0.55      inference('simplify', [status(thm)], ['54'])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X0)
% 0.36/0.55          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['53', '55'])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['52', '58'])).
% 0.36/0.55  thf('60', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf(t7_ordinal1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.55  thf('63', plain,
% 0.36/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.55  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('sup-', [status(thm)], ['60', '63'])).
% 0.36/0.55  thf('65', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['59', '64'])).
% 0.36/0.55  thf(fc2_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      (![X26 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.36/0.55          | ~ (l1_struct_0 @ X26)
% 0.36/0.55          | (v2_struct_0 @ X26))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1)))
% 0.36/0.55         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.55  thf('68', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      ((~ (l1_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['67', '68'])).
% 0.36/0.55  thf('70', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['25', '69'])).
% 0.36/0.55  thf('71', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('72', plain, (~ ((r1_tsep_1 @ sk_B_1 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.55  thf('73', plain,
% 0.36/0.55      (((r1_tsep_1 @ sk_C @ sk_B_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_C))),
% 0.36/0.55      inference('split', [status(esa)], ['5'])).
% 0.36/0.55  thf('74', plain, (((r1_tsep_1 @ sk_C @ sk_B_1))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      ((~ (l1_struct_0 @ sk_B_1)
% 0.36/0.55        | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | ~ (l1_struct_0 @ sk_C))),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['24', '74'])).
% 0.36/0.55  thf('76', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_B_1)
% 0.36/0.55        | ~ (l1_struct_0 @ sk_C)
% 0.36/0.55        | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '75'])).
% 0.36/0.55  thf('77', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('78', plain,
% 0.36/0.55      ((~ (l1_struct_0 @ sk_C)
% 0.36/0.55        | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_C)
% 0.36/0.55        | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '78'])).
% 0.36/0.55  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('81', plain,
% 0.36/0.55      ((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.55  thf('82', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X1 @ X0)
% 0.36/0.55          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.36/0.55          | (r1_tarski @ X1 @ k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf('83', plain,
% 0.36/0.55      (((r1_tarski @ (u1_struct_0 @ sk_B_1) @ k1_xboole_0)
% 0.36/0.55        | ~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.55  thf('84', plain,
% 0.36/0.55      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.55  thf('85', plain, ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ k1_xboole_0)),
% 0.36/0.55      inference('demod', [status(thm)], ['83', '84'])).
% 0.36/0.55  thf('86', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i]:
% 0.36/0.55         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.36/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.55  thf('87', plain,
% 0.36/0.55      (((k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.55  thf('88', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.55  thf('89', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.36/0.55  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('sup-', [status(thm)], ['60', '63'])).
% 0.36/0.55  thf('91', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.36/0.55  thf('92', plain,
% 0.36/0.55      (![X26 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.36/0.55          | ~ (l1_struct_0 @ X26)
% 0.36/0.55          | (v2_struct_0 @ X26))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.55  thf('93', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.36/0.55  thf('94', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('95', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.36/0.55      inference('clc', [status(thm)], ['93', '94'])).
% 0.36/0.55  thf('96', plain, (~ (l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '95'])).
% 0.36/0.55  thf('97', plain, ((l1_pre_topc @ sk_B_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('98', plain, ($false), inference('demod', [status(thm)], ['96', '97'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
