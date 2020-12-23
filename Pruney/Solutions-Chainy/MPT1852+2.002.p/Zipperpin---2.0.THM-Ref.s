%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kB3bSWc6qX

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 (3387 expanded)
%              Number of leaves         :   27 ( 979 expanded)
%              Depth                    :   28
%              Number of atoms          : 1162 (36647 expanded)
%              Number of equality atoms :   15 (1078 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ X20 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t19_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v3_tdlat_3 @ A ) )
           => ( v3_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v3_tdlat_3 @ A ) )
             => ( v3_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_tex_2])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ( m1_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('22',plain,
    ( ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X18 ) @ ( u1_pre_topc @ X18 ) ) )
      | ( m1_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf(d3_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
             => ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tdlat_3 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_tarski @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_tdlat_3 @ X28 )
      | ~ ( r2_hidden @ X29 @ ( u1_pre_topc @ X28 ) )
      | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X28 ) @ X29 ) @ ( u1_pre_topc @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('57',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ X23 @ X24 )
      | ( X23 != X21 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('59',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v3_pre_topc @ X21 @ X24 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ X0 )
      | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_A @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('63',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('65',plain,(
    ! [X28: $i] :
      ( ( r2_hidden @ ( sk_B @ X28 ) @ ( u1_pre_topc @ X28 ) )
      | ( v3_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('66',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v3_tdlat_3 @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['61','62','63','64','77'])).

thf('79',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['55','78'])).

thf('80',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['50','79'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('81',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('82',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('88',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('94',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X28 ) @ ( sk_B @ X28 ) ) @ ( u1_pre_topc @ X28 ) )
      | ( v3_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['92','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('102',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('103',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','34'])).

thf('104',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v3_pre_topc @ X21 @ X24 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ~ ( m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('109',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['50','79'])).

thf('113',plain,(
    v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['107','113','114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['100','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kB3bSWc6qX
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 205 iterations in 0.125s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.59  thf(t2_tsep_1, axiom,
% 0.20/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 0.20/0.59      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.59  thf(t65_pre_topc, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( l1_pre_topc @ B ) =>
% 0.20/0.59           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.59             ( m1_pre_topc @
% 0.20/0.59               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X19)
% 0.20/0.59          | ~ (m1_pre_topc @ X20 @ X19)
% 0.20/0.59          | (m1_pre_topc @ X20 @ 
% 0.20/0.59             (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))
% 0.20/0.59          | ~ (l1_pre_topc @ X20))),
% 0.20/0.59      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0)
% 0.20/0.59          | (m1_pre_topc @ X0 @ 
% 0.20/0.59             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.59          | ~ (l1_pre_topc @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((m1_pre_topc @ X0 @ 
% 0.20/0.59           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.59          | ~ (l1_pre_topc @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.59  thf(t19_tex_2, conjecture,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( l1_pre_topc @ B ) =>
% 0.20/0.59           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.59                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.59               ( v3_tdlat_3 @ A ) ) =>
% 0.20/0.59             ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i]:
% 0.20/0.59        ( ( l1_pre_topc @ A ) =>
% 0.20/0.59          ( ![B:$i]:
% 0.20/0.59            ( ( l1_pre_topc @ B ) =>
% 0.20/0.59              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.59                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.59                  ( v3_tdlat_3 @ A ) ) =>
% 0.20/0.59                ( v3_tdlat_3 @ B ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t19_tex_2])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t59_pre_topc, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_pre_topc @
% 0.20/0.59             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.59           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X17 @ 
% 0.20/0.59             (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.20/0.59          | (m1_pre_topc @ X17 @ X18)
% 0.20/0.59          | ~ (l1_pre_topc @ X18))),
% 0.20/0.59      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.59             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.59          | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.59          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.59  thf('7', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.59             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.59          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.59  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.59  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('11', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.20/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf(t1_tsep_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.59           ( m1_subset_1 @
% 0.20/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.59          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.20/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.59          | ~ (l1_pre_topc @ X26))),
% 0.20/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_B_1)
% 0.20/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.59  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.59  thf(t3_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.59  thf(d10_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X0 : $i, X2 : $i]:
% 0.20/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.59        | ((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((m1_pre_topc @ X0 @ 
% 0.20/0.59           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.59          | ~ (l1_pre_topc @ X0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (((m1_pre_topc @ sk_B_1 @ 
% 0.20/0.59         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('23', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      ((m1_pre_topc @ sk_B_1 @ 
% 0.20/0.59        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X17 @ 
% 0.20/0.59             (g1_pre_topc @ (u1_struct_0 @ X18) @ (u1_pre_topc @ X18)))
% 0.20/0.59          | (m1_pre_topc @ X17 @ X18)
% 0.20/0.59          | ~ (l1_pre_topc @ X18))),
% 0.20/0.59      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.59  thf('26', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.59  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('28', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i]:
% 0.20/0.59         (~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.59          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.20/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.59          | ~ (l1_pre_topc @ X26))),
% 0.20/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.20/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.59  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.59  thf('33', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.59  thf('35', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '34'])).
% 0.20/0.59  thf(d3_tdlat_3, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.59         ( ![B:$i]:
% 0.20/0.59           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59             ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.59               ( r2_hidden @
% 0.20/0.59                 ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.59                 ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (![X28 : $i]:
% 0.20/0.59         ((m1_subset_1 @ (sk_B @ X28) @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.59          | (v3_tdlat_3 @ X28)
% 0.20/0.59          | ~ (l1_pre_topc @ X28))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X0)
% 0.20/0.59          | (v3_tdlat_3 @ X0)
% 0.20/0.59          | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.59  thf('39', plain,
% 0.20/0.59      (((r1_tarski @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.59        | (v3_tdlat_3 @ sk_B_1)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.59  thf('40', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (((r1_tarski @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.59        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.59  thf('42', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('43', plain, ((r1_tarski @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      (![X3 : $i, X5 : $i]:
% 0.20/0.59         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('45', plain,
% 0.20/0.59      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      (![X28 : $i, X29 : $i]:
% 0.20/0.59         (~ (v3_tdlat_3 @ X28)
% 0.20/0.59          | ~ (r2_hidden @ X29 @ (u1_pre_topc @ X28))
% 0.20/0.59          | (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X28) @ X29) @ 
% 0.20/0.59             (u1_pre_topc @ X28))
% 0.20/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.59          | ~ (l1_pre_topc @ X28))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | (r2_hidden @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59           (u1_pre_topc @ sk_A))
% 0.20/0.59        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.59        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.59  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('49', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('50', plain,
% 0.20/0.59      (((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59         (u1_pre_topc @ sk_A))
% 0.20/0.59        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.59  thf('51', plain,
% 0.20/0.59      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf(d5_pre_topc, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.59             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.59          | ~ (v3_pre_topc @ X9 @ X10)
% 0.20/0.59          | (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.20/0.59          | ~ (l1_pre_topc @ X10))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.59        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.59  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('55', plain,
% 0.20/0.59      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.59        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.59  thf('56', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '34'])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf(t33_tops_2, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.59               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.59                 ( ![D:$i]:
% 0.20/0.59                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.59                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('58', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.59          | ~ (v3_pre_topc @ X21 @ X22)
% 0.20/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.59          | (v3_pre_topc @ X23 @ X24)
% 0.20/0.59          | ((X23) != (X21))
% 0.20/0.59          | ~ (m1_pre_topc @ X24 @ X22)
% 0.20/0.59          | ~ (l1_pre_topc @ X22))),
% 0.20/0.59      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X22)
% 0.20/0.59          | ~ (m1_pre_topc @ X24 @ X22)
% 0.20/0.59          | (v3_pre_topc @ X21 @ X24)
% 0.20/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.59          | ~ (v3_pre_topc @ X21 @ X22)
% 0.20/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.20/0.59      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.59          | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ X0)
% 0.20/0.59          | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.20/0.59          | ~ (l1_pre_topc @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['57', '59'])).
% 0.20/0.59  thf('61', plain,
% 0.20/0.59      ((~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_A @ sk_B_1)
% 0.20/0.59        | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A)
% 0.20/0.59        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['56', '60'])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('63', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('64', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.20/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf('65', plain,
% 0.20/0.59      (![X28 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_B @ X28) @ (u1_pre_topc @ X28))
% 0.20/0.59          | (v3_tdlat_3 @ X28)
% 0.20/0.59          | ~ (l1_pre_topc @ X28))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('67', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '34'])).
% 0.20/0.59  thf('68', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.59          | ~ (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.20/0.59          | (v3_pre_topc @ X9 @ X10)
% 0.20/0.59          | ~ (l1_pre_topc @ X10))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.59  thf('69', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59          | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.59          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.20/0.59          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.59  thf('70', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('71', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.20/0.59          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.59      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.59  thf('72', plain,
% 0.20/0.59      ((~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.20/0.59        | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['66', '71'])).
% 0.20/0.59  thf('73', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_B_1)
% 0.20/0.59        | (v3_tdlat_3 @ sk_B_1)
% 0.20/0.59        | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['65', '72'])).
% 0.20/0.59  thf('74', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('75', plain,
% 0.20/0.59      (((v3_tdlat_3 @ sk_B_1) | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.59  thf('76', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('77', plain, ((v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.20/0.59      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.59  thf('78', plain, ((v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A)),
% 0.20/0.59      inference('demod', [status(thm)], ['61', '62', '63', '64', '77'])).
% 0.20/0.59  thf('79', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['55', '78'])).
% 0.20/0.59  thf('80', plain,
% 0.20/0.59      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        (u1_pre_topc @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['50', '79'])).
% 0.20/0.59  thf(dt_u1_pre_topc, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( m1_subset_1 @
% 0.20/0.59         ( u1_pre_topc @ A ) @ 
% 0.20/0.59         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.59  thf('81', plain,
% 0.20/0.59      (![X13 : $i]:
% 0.20/0.59         ((m1_subset_1 @ (u1_pre_topc @ X13) @ 
% 0.20/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.20/0.59          | ~ (l1_pre_topc @ X13))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.59  thf(t4_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.59       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.59  thf('82', plain,
% 0.20/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.20/0.59          | (m1_subset_1 @ X6 @ X8))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.59  thf('83', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X0)
% 0.20/0.59          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.59          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.59  thf('84', plain,
% 0.20/0.59      (((m1_subset_1 @ 
% 0.20/0.59         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['80', '83'])).
% 0.20/0.59  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('86', plain,
% 0.20/0.59      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.59  thf('87', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '34'])).
% 0.20/0.59  thf('88', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.59          | ~ (v3_pre_topc @ X9 @ X10)
% 0.20/0.59          | (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.20/0.59          | ~ (l1_pre_topc @ X10))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.59  thf('89', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59          | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.59          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.20/0.59          | ~ (v3_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.59  thf('90', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('91', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.20/0.59          | ~ (v3_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.59  thf('92', plain,
% 0.20/0.59      ((~ (v3_pre_topc @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)
% 0.20/0.59        | (r2_hidden @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59           (u1_pre_topc @ sk_B_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['86', '91'])).
% 0.20/0.59  thf('93', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '34'])).
% 0.20/0.59  thf('94', plain,
% 0.20/0.59      (![X28 : $i]:
% 0.20/0.59         (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X28) @ (sk_B @ X28)) @ 
% 0.20/0.59             (u1_pre_topc @ X28))
% 0.20/0.59          | (v3_tdlat_3 @ X28)
% 0.20/0.59          | ~ (l1_pre_topc @ X28))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.59  thf('95', plain,
% 0.20/0.59      ((~ (r2_hidden @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59           (u1_pre_topc @ sk_B_1))
% 0.20/0.59        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.59        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.59  thf('96', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('97', plain,
% 0.20/0.59      ((~ (r2_hidden @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59           (u1_pre_topc @ sk_B_1))
% 0.20/0.59        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.59  thf('98', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('99', plain,
% 0.20/0.59      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59          (u1_pre_topc @ sk_B_1))),
% 0.20/0.59      inference('clc', [status(thm)], ['97', '98'])).
% 0.20/0.59  thf('100', plain,
% 0.20/0.59      (~ (v3_pre_topc @ 
% 0.20/0.59          (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 0.20/0.59      inference('clc', [status(thm)], ['92', '99'])).
% 0.20/0.59  thf('101', plain,
% 0.20/0.59      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.59  thf('102', plain,
% 0.20/0.59      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.59  thf('103', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '34'])).
% 0.20/0.59  thf('104', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X22)
% 0.20/0.59          | ~ (m1_pre_topc @ X24 @ X22)
% 0.20/0.59          | (v3_pre_topc @ X21 @ X24)
% 0.20/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.59          | ~ (v3_pre_topc @ X21 @ X22)
% 0.20/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.20/0.59      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.59  thf('105', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.59          | ~ (v3_pre_topc @ X0 @ X1)
% 0.20/0.59          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 0.20/0.59          | ~ (l1_pre_topc @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.59  thf('106', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (l1_pre_topc @ X0)
% 0.20/0.59          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.20/0.59          | (v3_pre_topc @ 
% 0.20/0.59             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)
% 0.20/0.59          | ~ (v3_pre_topc @ 
% 0.20/0.59               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ X0)
% 0.20/0.59          | ~ (m1_subset_1 @ 
% 0.20/0.59               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['102', '105'])).
% 0.20/0.59  thf('107', plain,
% 0.20/0.59      ((~ (v3_pre_topc @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)
% 0.20/0.59        | (v3_pre_topc @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)
% 0.20/0.59        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['101', '106'])).
% 0.20/0.59  thf('108', plain,
% 0.20/0.59      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.59  thf('109', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.59          | ~ (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.20/0.59          | (v3_pre_topc @ X9 @ X10)
% 0.20/0.59          | ~ (l1_pre_topc @ X10))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.59  thf('110', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | (v3_pre_topc @ 
% 0.20/0.59           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)
% 0.20/0.59        | ~ (r2_hidden @ 
% 0.20/0.59             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59             (u1_pre_topc @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.59  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('112', plain,
% 0.20/0.59      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        (u1_pre_topc @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['50', '79'])).
% 0.20/0.59  thf('113', plain,
% 0.20/0.59      ((v3_pre_topc @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        sk_A)),
% 0.20/0.59      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.20/0.59  thf('114', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.59  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('116', plain,
% 0.20/0.59      ((v3_pre_topc @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.59        sk_B_1)),
% 0.20/0.59      inference('demod', [status(thm)], ['107', '113', '114', '115'])).
% 0.20/0.59  thf('117', plain, ($false), inference('demod', [status(thm)], ['100', '116'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
