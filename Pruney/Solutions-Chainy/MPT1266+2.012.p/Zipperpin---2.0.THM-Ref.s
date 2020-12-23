%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vnJmQZnI1U

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:13 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  163 (1059 expanded)
%              Number of leaves         :   36 ( 324 expanded)
%              Depth                    :   22
%              Number of atoms          : 1286 (9794 expanded)
%              Number of equality atoms :   92 ( 656 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t84_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( ( k1_tops_1 @ A @ B )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tops_1])).

thf('0',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tops_1 @ X29 @ X30 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('13',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','26'])).

thf('28',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('33',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v1_tops_1 @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = ( k2_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('52',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('71',plain,(
    ! [X9: $i] :
      ( ( k1_subset_1 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X17: $i] :
      ( ( k2_subset_1 @ X17 )
      = ( k3_subset_1 @ X17 @ ( k1_subset_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('73',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('74',plain,(
    ! [X17: $i] :
      ( X17
      = ( k3_subset_1 @ X17 @ ( k1_subset_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('78',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','76','77'])).

thf('79',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('87',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('96',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('99',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('100',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('102',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('105',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('107',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_pre_topc @ X28 @ X27 )
       != ( k2_struct_0 @ X28 ) )
      | ( v1_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('114',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ( v2_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('121',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','121'])).

thf('123',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','94','95','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vnJmQZnI1U
% 0.15/0.37  % Computer   : n004.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:50:54 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.85/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.03  % Solved by: fo/fo7.sh
% 0.85/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.03  % done 2155 iterations in 0.580s
% 0.85/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.03  % SZS output start Refutation
% 0.85/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.85/1.03  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.85/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.03  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.85/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.85/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.85/1.03  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.85/1.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.85/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.03  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.85/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.85/1.03  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.85/1.03  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.85/1.03  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.85/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.85/1.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.85/1.03  thf(t84_tops_1, conjecture,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( v2_tops_1 @ B @ A ) <=>
% 0.85/1.03             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.85/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.03    (~( ![A:$i]:
% 0.85/1.03        ( ( l1_pre_topc @ A ) =>
% 0.85/1.03          ( ![B:$i]:
% 0.85/1.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03              ( ( v2_tops_1 @ B @ A ) <=>
% 0.85/1.03                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.85/1.03    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.85/1.03  thf('0', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.85/1.03        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('1', plain,
% 0.85/1.03      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.85/1.03       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('split', [status(esa)], ['0'])).
% 0.85/1.03  thf('2', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('3', plain,
% 0.85/1.03      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('split', [status(esa)], ['2'])).
% 0.85/1.03  thf('4', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(d4_tops_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( v2_tops_1 @ B @ A ) <=>
% 0.85/1.03             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.85/1.03  thf('5', plain,
% 0.85/1.03      (![X29 : $i, X30 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.85/1.03          | ~ (v2_tops_1 @ X29 @ X30)
% 0.85/1.03          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.85/1.03          | ~ (l1_pre_topc @ X30))),
% 0.85/1.03      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.85/1.03  thf('6', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.03        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.85/1.03        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.85/1.03  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('8', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(d5_subset_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.03       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.85/1.03  thf('9', plain,
% 0.85/1.03      (![X11 : $i, X12 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.85/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.03  thf('10', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.85/1.03  thf(d3_struct_0, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.85/1.03  thf('11', plain,
% 0.85/1.03      (![X21 : $i]:
% 0.85/1.03         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.03  thf('12', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.85/1.03  thf('13', plain,
% 0.85/1.03      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.85/1.03        | ~ (l1_struct_0 @ sk_A))),
% 0.85/1.03      inference('sup+', [status(thm)], ['11', '12'])).
% 0.85/1.03  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(dt_l1_pre_topc, axiom,
% 0.85/1.03    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.85/1.03  thf('15', plain,
% 0.85/1.03      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.85/1.03  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.85/1.03  thf('17', plain,
% 0.85/1.03      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['13', '16'])).
% 0.85/1.03  thf('18', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['10', '17'])).
% 0.85/1.03  thf('19', plain,
% 0.85/1.03      (![X21 : $i]:
% 0.85/1.03         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.03  thf('20', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('21', plain,
% 0.85/1.03      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.85/1.03        | ~ (l1_struct_0 @ sk_A))),
% 0.85/1.03      inference('sup+', [status(thm)], ['19', '20'])).
% 0.85/1.03  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.85/1.03  thf('23', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['21', '22'])).
% 0.85/1.03  thf('24', plain,
% 0.85/1.03      (![X11 : $i, X12 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.85/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.03  thf('25', plain,
% 0.85/1.03      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('sup-', [status(thm)], ['23', '24'])).
% 0.85/1.03  thf('26', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['18', '25'])).
% 0.85/1.03  thf('27', plain,
% 0.85/1.03      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.85/1.03        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('demod', [status(thm)], ['6', '7', '26'])).
% 0.85/1.03  thf('28', plain,
% 0.85/1.03      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['3', '27'])).
% 0.85/1.03  thf('29', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(dt_k3_subset_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.03       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.85/1.03  thf('30', plain,
% 0.85/1.03      (![X13 : $i, X14 : $i]:
% 0.85/1.03         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.85/1.03          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.85/1.03  thf('31', plain,
% 0.85/1.03      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['29', '30'])).
% 0.85/1.03  thf('32', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['18', '25'])).
% 0.85/1.03  thf('33', plain,
% 0.85/1.03      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['31', '32'])).
% 0.85/1.03  thf(d3_tops_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( v1_tops_1 @ B @ A ) <=>
% 0.85/1.03             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.85/1.03  thf('34', plain,
% 0.85/1.03      (![X27 : $i, X28 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.85/1.03          | ~ (v1_tops_1 @ X27 @ X28)
% 0.85/1.03          | ((k2_pre_topc @ X28 @ X27) = (k2_struct_0 @ X28))
% 0.85/1.03          | ~ (l1_pre_topc @ X28))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.85/1.03  thf('35', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.03        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.85/1.03            = (k2_struct_0 @ sk_A))
% 0.85/1.03        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.85/1.03  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('37', plain,
% 0.85/1.03      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.85/1.03          = (k2_struct_0 @ sk_A))
% 0.85/1.03        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.85/1.03      inference('demod', [status(thm)], ['35', '36'])).
% 0.85/1.03  thf('38', plain,
% 0.85/1.03      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.85/1.03          = (k2_struct_0 @ sk_A)))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['28', '37'])).
% 0.85/1.03  thf('39', plain,
% 0.85/1.03      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['31', '32'])).
% 0.85/1.03  thf(dt_k2_pre_topc, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.85/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.85/1.03       ( m1_subset_1 @
% 0.85/1.03         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.85/1.03  thf('40', plain,
% 0.85/1.03      (![X22 : $i, X23 : $i]:
% 0.85/1.03         (~ (l1_pre_topc @ X22)
% 0.85/1.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.85/1.03          | (m1_subset_1 @ (k2_pre_topc @ X22 @ X23) @ 
% 0.85/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.85/1.03  thf('41', plain,
% 0.85/1.03      (((m1_subset_1 @ 
% 0.85/1.03         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.85/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.85/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['39', '40'])).
% 0.85/1.03  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('43', plain,
% 0.85/1.03      ((m1_subset_1 @ 
% 0.85/1.03        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['41', '42'])).
% 0.85/1.03  thf('44', plain,
% 0.85/1.03      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['38', '43'])).
% 0.85/1.03  thf(involutiveness_k3_subset_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.03       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.85/1.03  thf('45', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 0.85/1.03          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.85/1.03      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.85/1.03  thf('46', plain,
% 0.85/1.03      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.03          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.85/1.03          = (k2_struct_0 @ sk_A)))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.85/1.03  thf('47', plain,
% 0.85/1.03      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['38', '43'])).
% 0.85/1.03  thf('48', plain,
% 0.85/1.03      (![X11 : $i, X12 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.85/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.03  thf('49', plain,
% 0.85/1.03      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.85/1.03          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['47', '48'])).
% 0.85/1.03  thf('50', plain,
% 0.85/1.03      (![X21 : $i]:
% 0.85/1.03         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.03  thf('51', plain,
% 0.85/1.03      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.85/1.03          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['47', '48'])).
% 0.85/1.03  thf('52', plain,
% 0.85/1.03      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.85/1.03           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.85/1.03         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['50', '51'])).
% 0.85/1.03  thf(d3_tarski, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_tarski @ A @ B ) <=>
% 0.85/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.85/1.03  thf('53', plain,
% 0.85/1.03      (![X1 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('54', plain,
% 0.85/1.03      (![X1 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('55', plain,
% 0.85/1.03      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['53', '54'])).
% 0.85/1.03  thf('56', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.85/1.03      inference('simplify', [status(thm)], ['55'])).
% 0.85/1.03  thf(l32_xboole_1, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.85/1.03  thf('57', plain,
% 0.85/1.03      (![X4 : $i, X6 : $i]:
% 0.85/1.03         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.85/1.03      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.85/1.03  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['56', '57'])).
% 0.85/1.03  thf('59', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.85/1.03      inference('simplify', [status(thm)], ['55'])).
% 0.85/1.03  thf(t3_subset, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.85/1.03  thf('60', plain,
% 0.85/1.03      (![X18 : $i, X20 : $i]:
% 0.85/1.03         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.85/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.85/1.03  thf('61', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['59', '60'])).
% 0.85/1.03  thf('62', plain,
% 0.85/1.03      (![X13 : $i, X14 : $i]:
% 0.85/1.03         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.85/1.03          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.85/1.03      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.85/1.03  thf('63', plain,
% 0.85/1.03      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['61', '62'])).
% 0.85/1.03  thf('64', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['59', '60'])).
% 0.85/1.03  thf('65', plain,
% 0.85/1.03      (![X11 : $i, X12 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.85/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.03  thf('66', plain,
% 0.85/1.03      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['64', '65'])).
% 0.85/1.03  thf('67', plain,
% 0.85/1.03      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('demod', [status(thm)], ['63', '66'])).
% 0.85/1.03  thf('68', plain,
% 0.85/1.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['58', '67'])).
% 0.85/1.03  thf('69', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 0.85/1.03          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.85/1.03      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.85/1.03  thf('70', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.85/1.03      inference('sup-', [status(thm)], ['68', '69'])).
% 0.85/1.03  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.85/1.03  thf('71', plain, (![X9 : $i]: ((k1_subset_1 @ X9) = (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.85/1.03  thf(t22_subset_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.85/1.03  thf('72', plain,
% 0.85/1.03      (![X17 : $i]:
% 0.85/1.03         ((k2_subset_1 @ X17) = (k3_subset_1 @ X17 @ (k1_subset_1 @ X17)))),
% 0.85/1.03      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.85/1.03  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.85/1.03  thf('73', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.85/1.03      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.85/1.03  thf('74', plain,
% 0.85/1.03      (![X17 : $i]: ((X17) = (k3_subset_1 @ X17 @ (k1_subset_1 @ X17)))),
% 0.85/1.03      inference('demod', [status(thm)], ['72', '73'])).
% 0.85/1.03  thf('75', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['71', '74'])).
% 0.85/1.03  thf('76', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.03      inference('demod', [status(thm)], ['70', '75'])).
% 0.85/1.03  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.85/1.03  thf('78', plain,
% 0.85/1.03      ((((k1_xboole_0)
% 0.85/1.03          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['52', '76', '77'])).
% 0.85/1.03  thf('79', plain,
% 0.85/1.03      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.85/1.03          = (k1_xboole_0)))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['49', '78'])).
% 0.85/1.03  thf('80', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['71', '74'])).
% 0.85/1.03  thf('81', plain,
% 0.85/1.03      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['46', '79', '80'])).
% 0.85/1.03  thf('82', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf(d1_tops_1, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ( l1_pre_topc @ A ) =>
% 0.85/1.03       ( ![B:$i]:
% 0.85/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.03           ( ( k1_tops_1 @ A @ B ) =
% 0.85/1.03             ( k3_subset_1 @
% 0.85/1.03               ( u1_struct_0 @ A ) @ 
% 0.85/1.03               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.85/1.03  thf('83', plain,
% 0.85/1.03      (![X25 : $i, X26 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.85/1.03          | ((k1_tops_1 @ X26 @ X25)
% 0.85/1.03              = (k3_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.85/1.03                 (k2_pre_topc @ X26 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25))))
% 0.85/1.03          | ~ (l1_pre_topc @ X26))),
% 0.85/1.03      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.85/1.03  thf('84', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.03        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.85/1.03            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.03               (k2_pre_topc @ sk_A @ 
% 0.85/1.03                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['82', '83'])).
% 0.85/1.03  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('86', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['18', '25'])).
% 0.85/1.03  thf('87', plain,
% 0.85/1.03      (((k1_tops_1 @ sk_A @ sk_B)
% 0.85/1.03         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.03            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.85/1.03      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.85/1.03  thf('88', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.85/1.03          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.85/1.03             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['81', '87'])).
% 0.85/1.03  thf('89', plain,
% 0.85/1.03      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.85/1.03          = (k2_struct_0 @ sk_A)))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['28', '37'])).
% 0.85/1.03  thf('90', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.03      inference('demod', [status(thm)], ['70', '75'])).
% 0.85/1.03  thf('91', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.85/1.03         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.85/1.03  thf('92', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.85/1.03         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('split', [status(esa)], ['0'])).
% 0.85/1.03  thf('93', plain,
% 0.85/1.03      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.85/1.03         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.85/1.03             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['91', '92'])).
% 0.85/1.03  thf('94', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.85/1.03       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('simplify', [status(thm)], ['93'])).
% 0.85/1.03  thf('95', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.85/1.03       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('split', [status(esa)], ['2'])).
% 0.85/1.03  thf('96', plain,
% 0.85/1.03      (![X21 : $i]:
% 0.85/1.03         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.85/1.03  thf('97', plain,
% 0.85/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('split', [status(esa)], ['2'])).
% 0.85/1.03  thf('98', plain,
% 0.85/1.03      ((m1_subset_1 @ 
% 0.85/1.03        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['41', '42'])).
% 0.85/1.03  thf('99', plain,
% 0.85/1.03      (![X15 : $i, X16 : $i]:
% 0.85/1.03         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 0.85/1.03          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.85/1.03      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.85/1.03  thf('100', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.03         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.03          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.85/1.03         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['98', '99'])).
% 0.85/1.03  thf('101', plain,
% 0.85/1.03      (((k1_tops_1 @ sk_A @ sk_B)
% 0.85/1.03         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.85/1.03            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.85/1.03      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.85/1.03  thf('102', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.85/1.03         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.85/1.03      inference('demod', [status(thm)], ['100', '101'])).
% 0.85/1.03  thf('103', plain,
% 0.85/1.03      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.85/1.03          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('sup+', [status(thm)], ['97', '102'])).
% 0.85/1.03  thf('104', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['71', '74'])).
% 0.85/1.03  thf('105', plain,
% 0.85/1.03      ((((u1_struct_0 @ sk_A)
% 0.85/1.03          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('demod', [status(thm)], ['103', '104'])).
% 0.85/1.03  thf('106', plain,
% 0.85/1.03      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.85/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['31', '32'])).
% 0.85/1.03  thf('107', plain,
% 0.85/1.03      (![X27 : $i, X28 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.85/1.03          | ((k2_pre_topc @ X28 @ X27) != (k2_struct_0 @ X28))
% 0.85/1.03          | (v1_tops_1 @ X27 @ X28)
% 0.85/1.03          | ~ (l1_pre_topc @ X28))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.85/1.03  thf('108', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.03        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.85/1.03        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.85/1.03            != (k2_struct_0 @ sk_A)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['106', '107'])).
% 0.85/1.03  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('110', plain,
% 0.85/1.03      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.85/1.03        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.85/1.03            != (k2_struct_0 @ sk_A)))),
% 0.85/1.03      inference('demod', [status(thm)], ['108', '109'])).
% 0.85/1.03  thf('111', plain,
% 0.85/1.03      (((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.85/1.03         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['105', '110'])).
% 0.85/1.03  thf('112', plain,
% 0.85/1.03      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.85/1.03         | ~ (l1_struct_0 @ sk_A)
% 0.85/1.03         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['96', '111'])).
% 0.85/1.03  thf('113', plain, ((l1_struct_0 @ sk_A)),
% 0.85/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.85/1.03  thf('114', plain,
% 0.85/1.03      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.85/1.03         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('demod', [status(thm)], ['112', '113'])).
% 0.85/1.03  thf('115', plain,
% 0.85/1.03      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('simplify', [status(thm)], ['114'])).
% 0.85/1.03  thf('116', plain,
% 0.85/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('117', plain,
% 0.85/1.03      (![X29 : $i, X30 : $i]:
% 0.85/1.03         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.85/1.03          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.85/1.03          | (v2_tops_1 @ X29 @ X30)
% 0.85/1.03          | ~ (l1_pre_topc @ X30))),
% 0.85/1.03      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.85/1.03  thf('118', plain,
% 0.85/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.03        | (v2_tops_1 @ sk_B @ sk_A)
% 0.85/1.03        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.85/1.03  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('120', plain,
% 0.85/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.85/1.03         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.85/1.03      inference('demod', [status(thm)], ['18', '25'])).
% 0.85/1.03  thf('121', plain,
% 0.85/1.03      (((v2_tops_1 @ sk_B @ sk_A)
% 0.85/1.03        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.85/1.03      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.85/1.03  thf('122', plain,
% 0.85/1.03      (((v2_tops_1 @ sk_B @ sk_A))
% 0.85/1.03         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.85/1.03      inference('sup-', [status(thm)], ['115', '121'])).
% 0.85/1.03  thf('123', plain,
% 0.85/1.03      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.85/1.03      inference('split', [status(esa)], ['0'])).
% 0.85/1.03  thf('124', plain,
% 0.85/1.03      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.85/1.03       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['122', '123'])).
% 0.85/1.03  thf('125', plain, ($false),
% 0.85/1.03      inference('sat_resolution*', [status(thm)], ['1', '94', '95', '124'])).
% 0.85/1.03  
% 0.85/1.03  % SZS output end Refutation
% 0.85/1.03  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
