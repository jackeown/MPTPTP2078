%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ttYqWZJN3d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:33 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  176 (1456 expanded)
%              Number of leaves         :   47 ( 411 expanded)
%              Depth                    :   19
%              Number of atoms          : 1318 (16815 expanded)
%              Number of equality atoms :   80 ( 937 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('14',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X57 @ X58 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ~ ( v1_tops_1 @ X65 @ X66 )
      | ( ( k2_pre_topc @ X66 @ X65 )
        = ( k2_struct_0 @ X66 ) )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('29',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X72 ) @ X71 ) @ X72 )
      | ~ ( v3_tops_1 @ X71 @ X72 )
      | ~ ( l1_pre_topc @ X72 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ~ ( r1_tarski @ X69 @ ( k2_tops_1 @ X70 @ X69 ) )
      | ( v2_tops_1 @ X69 @ X70 )
      | ~ ( l1_pre_topc @ X70 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t93_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('49',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X76 ) ) )
      | ( v3_tops_1 @ X75 @ X76 )
      | ~ ( v4_pre_topc @ X75 @ X76 )
      | ~ ( v2_tops_1 @ X75 @ X76 )
      | ~ ( l1_pre_topc @ X76 ) ) ),
    inference(cnf,[status(esa)],[t93_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('56',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('58',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['37','56','57'])).

thf('59',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['35','58'])).

thf('60',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['33','59'])).

thf('61',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','61'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('63',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('64',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( ( k1_tops_1 @ X62 @ X61 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X62 ) @ ( k2_pre_topc @ X62 @ ( k3_subset_1 @ ( u1_struct_0 @ X62 ) @ X61 ) ) ) )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('70',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('73',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X74 ) ) )
      | ( v2_tops_1 @ X73 @ X74 )
      | ~ ( v3_tops_1 @ X73 @ X74 )
      | ~ ( l1_pre_topc @ X74 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('79',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X68 ) ) )
      | ~ ( v2_tops_1 @ X67 @ X68 )
      | ( ( k1_tops_1 @ X68 @ X67 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X68 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['37','56','57'])).

thf('85',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','85'])).

thf('87',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','60'])).

thf('88',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('89',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('90',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('92',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','88','93'])).

thf('95',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['11','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k2_tops_1 @ X64 @ X63 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X64 ) @ ( k2_pre_topc @ X64 @ X63 ) @ ( k2_pre_topc @ X64 @ ( k3_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 ) ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( v4_pre_topc @ X59 @ X60 )
      | ( ( k2_pre_topc @ X60 @ X59 )
        = X59 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('107',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['98','99','105','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','88','93'])).

thf('109',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','88','93'])).

thf('110',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','60'])).

thf('111',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','88','93'])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('114',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('117',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('118',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k9_subset_1 @ X50 @ X48 @ X49 )
        = ( k3_xboole_0 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('119',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('120',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k9_subset_1 @ X50 @ X48 @ X49 )
        = ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','112','121'])).

thf('123',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['95','122'])).

thf('124',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('125',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['37','56'])).

thf('126',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ttYqWZJN3d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:05:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.61/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.83  % Solved by: fo/fo7.sh
% 0.61/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.83  % done 1235 iterations in 0.382s
% 0.61/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.83  % SZS output start Refutation
% 0.61/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.61/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.83  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.61/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.83  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.61/0.83  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.61/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.83  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.61/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.83  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.61/0.83  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.61/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.83  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.61/0.83  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.61/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.83  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.61/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.61/0.83  thf(d3_tarski, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.83  thf('0', plain,
% 0.61/0.83      (![X1 : $i, X3 : $i]:
% 0.61/0.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.83  thf(t94_tops_1, conjecture,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( v4_pre_topc @ B @ A ) =>
% 0.61/0.83             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.83    (~( ![A:$i]:
% 0.61/0.83        ( ( l1_pre_topc @ A ) =>
% 0.61/0.83          ( ![B:$i]:
% 0.61/0.83            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83              ( ( v4_pre_topc @ B @ A ) =>
% 0.61/0.83                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.61/0.83    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.61/0.83  thf('1', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(l3_subset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.61/0.83  thf('2', plain,
% 0.61/0.83      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X45 @ X46)
% 0.61/0.83          | (r2_hidden @ X45 @ X47)
% 0.61/0.83          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 0.61/0.83      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.61/0.83  thf('3', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.83  thf('4', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r1_tarski @ sk_B @ X0)
% 0.61/0.83          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['0', '3'])).
% 0.61/0.83  thf('5', plain,
% 0.61/0.83      (![X1 : $i, X3 : $i]:
% 0.61/0.83         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.83  thf('6', plain,
% 0.61/0.83      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.61/0.83        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.83  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.61/0.83      inference('simplify', [status(thm)], ['6'])).
% 0.61/0.83  thf(t28_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.61/0.83  thf('8', plain,
% 0.61/0.83      (![X9 : $i, X10 : $i]:
% 0.61/0.83         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.61/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.83  thf(t12_setfam_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.83  thf('9', plain,
% 0.61/0.83      (![X52 : $i, X53 : $i]:
% 0.61/0.83         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.61/0.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.61/0.83  thf('10', plain,
% 0.61/0.83      (![X9 : $i, X10 : $i]:
% 0.61/0.83         (((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (X9))
% 0.61/0.83          | ~ (r1_tarski @ X9 @ X10))),
% 0.61/0.83      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.83  thf('11', plain,
% 0.61/0.83      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['7', '10'])).
% 0.61/0.83  thf('12', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(dt_k3_subset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.83       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.61/0.83  thf('13', plain,
% 0.61/0.83      (![X41 : $i, X42 : $i]:
% 0.61/0.83         ((m1_subset_1 @ (k3_subset_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))
% 0.61/0.83          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.61/0.83      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.61/0.83  thf('14', plain,
% 0.61/0.83      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.61/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.83  thf('15', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(d5_subset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.83       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.61/0.83  thf('16', plain,
% 0.61/0.83      (![X39 : $i, X40 : $i]:
% 0.61/0.83         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 0.61/0.83          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.61/0.83      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.61/0.83  thf('17', plain,
% 0.61/0.83      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.61/0.83         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf('18', plain,
% 0.61/0.83      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.61/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('demod', [status(thm)], ['14', '17'])).
% 0.61/0.83  thf(dt_k2_pre_topc, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( ( l1_pre_topc @ A ) & 
% 0.61/0.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.83       ( m1_subset_1 @
% 0.61/0.83         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.61/0.83  thf('19', plain,
% 0.61/0.83      (![X57 : $i, X58 : $i]:
% 0.61/0.83         (~ (l1_pre_topc @ X57)
% 0.61/0.83          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.61/0.83          | (m1_subset_1 @ (k2_pre_topc @ X57 @ X58) @ 
% 0.61/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X57))))),
% 0.61/0.83      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.61/0.83  thf('20', plain,
% 0.61/0.83      (((m1_subset_1 @ 
% 0.61/0.83         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.61/0.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.83        | ~ (l1_pre_topc @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['18', '19'])).
% 0.61/0.83  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('22', plain,
% 0.61/0.83      ((m1_subset_1 @ 
% 0.61/0.83        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.61/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('demod', [status(thm)], ['20', '21'])).
% 0.61/0.83  thf('23', plain,
% 0.61/0.83      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.61/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('demod', [status(thm)], ['14', '17'])).
% 0.61/0.83  thf(d3_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( v1_tops_1 @ B @ A ) <=>
% 0.61/0.83             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.61/0.83  thf('24', plain,
% 0.61/0.83      (![X65 : $i, X66 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 0.61/0.83          | ~ (v1_tops_1 @ X65 @ X66)
% 0.61/0.83          | ((k2_pre_topc @ X66 @ X65) = (k2_struct_0 @ X66))
% 0.61/0.83          | ~ (l1_pre_topc @ X66))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.61/0.83  thf('25', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.61/0.83            = (k2_struct_0 @ sk_A))
% 0.61/0.83        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.61/0.83  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('27', plain,
% 0.61/0.83      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.61/0.83          = (k2_struct_0 @ sk_A))
% 0.61/0.83        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['25', '26'])).
% 0.61/0.83  thf('28', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t91_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( v3_tops_1 @ B @ A ) =>
% 0.61/0.83             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.61/0.83  thf('29', plain,
% 0.61/0.83      (![X71 : $i, X72 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 0.61/0.83          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X72) @ X71) @ X72)
% 0.61/0.83          | ~ (v3_tops_1 @ X71 @ X72)
% 0.61/0.83          | ~ (l1_pre_topc @ X72))),
% 0.61/0.83      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.61/0.83  thf('30', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.61/0.83        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['28', '29'])).
% 0.61/0.83  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('32', plain,
% 0.61/0.83      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.61/0.83         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf('33', plain,
% 0.61/0.83      ((~ (v3_tops_1 @ sk_B @ sk_A)
% 0.61/0.83        | (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.61/0.83  thf('34', plain,
% 0.61/0.83      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('35', plain,
% 0.61/0.83      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('split', [status(esa)], ['34'])).
% 0.61/0.83  thf('36', plain,
% 0.61/0.83      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('37', plain,
% 0.61/0.83      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('split', [status(esa)], ['36'])).
% 0.61/0.83  thf('38', plain,
% 0.61/0.83      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.61/0.83         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.61/0.83      inference('split', [status(esa)], ['34'])).
% 0.61/0.83  thf('39', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t88_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( v2_tops_1 @ B @ A ) <=>
% 0.61/0.83             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.61/0.83  thf('40', plain,
% 0.61/0.83      (![X69 : $i, X70 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 0.61/0.83          | ~ (r1_tarski @ X69 @ (k2_tops_1 @ X70 @ X69))
% 0.61/0.83          | (v2_tops_1 @ X69 @ X70)
% 0.61/0.83          | ~ (l1_pre_topc @ X70))),
% 0.61/0.83      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.61/0.83  thf('41', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | (v2_tops_1 @ sk_B @ sk_A)
% 0.61/0.83        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.61/0.83  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('43', plain,
% 0.61/0.83      (((v2_tops_1 @ sk_B @ sk_A)
% 0.61/0.83        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.83      inference('demod', [status(thm)], ['41', '42'])).
% 0.61/0.83  thf('44', plain,
% 0.61/0.83      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.61/0.83         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['38', '43'])).
% 0.61/0.83  thf(d10_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.83  thf('45', plain,
% 0.61/0.83      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.61/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.83  thf('46', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.61/0.83      inference('simplify', [status(thm)], ['45'])).
% 0.61/0.83  thf('47', plain,
% 0.61/0.83      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.61/0.83      inference('demod', [status(thm)], ['44', '46'])).
% 0.61/0.83  thf('48', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t93_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.61/0.83             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.61/0.83  thf('49', plain,
% 0.61/0.83      (![X75 : $i, X76 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (u1_struct_0 @ X76)))
% 0.61/0.83          | (v3_tops_1 @ X75 @ X76)
% 0.61/0.83          | ~ (v4_pre_topc @ X75 @ X76)
% 0.61/0.83          | ~ (v2_tops_1 @ X75 @ X76)
% 0.61/0.83          | ~ (l1_pre_topc @ X76))),
% 0.61/0.83      inference('cnf', [status(esa)], [t93_tops_1])).
% 0.61/0.83  thf('50', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ~ (v2_tops_1 @ sk_B @ sk_A)
% 0.61/0.83        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.61/0.83        | (v3_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['48', '49'])).
% 0.61/0.83  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('52', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('53', plain, ((~ (v2_tops_1 @ sk_B @ sk_A) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.61/0.83  thf('54', plain,
% 0.61/0.83      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['47', '53'])).
% 0.61/0.83  thf('55', plain,
% 0.61/0.83      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('split', [status(esa)], ['36'])).
% 0.61/0.83  thf('56', plain,
% 0.61/0.83      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['54', '55'])).
% 0.61/0.83  thf('57', plain,
% 0.61/0.83      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.83      inference('split', [status(esa)], ['34'])).
% 0.61/0.83  thf('58', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['37', '56', '57'])).
% 0.61/0.83  thf('59', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['35', '58'])).
% 0.61/0.83  thf('60', plain,
% 0.61/0.83      ((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.61/0.83      inference('demod', [status(thm)], ['33', '59'])).
% 0.61/0.83  thf('61', plain,
% 0.61/0.83      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.61/0.83         = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['27', '60'])).
% 0.61/0.83  thf('62', plain,
% 0.61/0.83      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.61/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('demod', [status(thm)], ['22', '61'])).
% 0.61/0.83  thf(involutiveness_k3_subset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.83       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.61/0.83  thf('63', plain,
% 0.61/0.83      (![X43 : $i, X44 : $i]:
% 0.61/0.83         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 0.61/0.83          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 0.61/0.83      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.61/0.83  thf('64', plain,
% 0.61/0.83      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.83         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.61/0.83         = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['62', '63'])).
% 0.61/0.83  thf('65', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(d1_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( k1_tops_1 @ A @ B ) =
% 0.61/0.83             ( k3_subset_1 @
% 0.61/0.83               ( u1_struct_0 @ A ) @ 
% 0.61/0.83               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.61/0.83  thf('66', plain,
% 0.61/0.83      (![X61 : $i, X62 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 0.61/0.83          | ((k1_tops_1 @ X62 @ X61)
% 0.61/0.83              = (k3_subset_1 @ (u1_struct_0 @ X62) @ 
% 0.61/0.83                 (k2_pre_topc @ X62 @ (k3_subset_1 @ (u1_struct_0 @ X62) @ X61))))
% 0.61/0.83          | ~ (l1_pre_topc @ X62))),
% 0.61/0.83      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.61/0.83  thf('67', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.61/0.83            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.83               (k2_pre_topc @ sk_A @ 
% 0.61/0.83                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['65', '66'])).
% 0.61/0.83  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('69', plain,
% 0.61/0.83      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.61/0.83         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf('70', plain,
% 0.61/0.83      (((k1_tops_1 @ sk_A @ sk_B)
% 0.61/0.83         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.83            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.61/0.83      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.61/0.83  thf('71', plain,
% 0.61/0.83      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('split', [status(esa)], ['34'])).
% 0.61/0.83  thf('72', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t92_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.61/0.83  thf('73', plain,
% 0.61/0.83      (![X73 : $i, X74 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (u1_struct_0 @ X74)))
% 0.61/0.83          | (v2_tops_1 @ X73 @ X74)
% 0.61/0.83          | ~ (v3_tops_1 @ X73 @ X74)
% 0.61/0.83          | ~ (l1_pre_topc @ X74))),
% 0.61/0.83      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.61/0.83  thf('74', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.61/0.83        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['72', '73'])).
% 0.61/0.83  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('76', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['74', '75'])).
% 0.61/0.83  thf('77', plain,
% 0.61/0.83      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['71', '76'])).
% 0.61/0.83  thf('78', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t84_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( v2_tops_1 @ B @ A ) <=>
% 0.61/0.83             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.61/0.83  thf('79', plain,
% 0.61/0.83      (![X67 : $i, X68 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X68)))
% 0.61/0.83          | ~ (v2_tops_1 @ X67 @ X68)
% 0.61/0.83          | ((k1_tops_1 @ X68 @ X67) = (k1_xboole_0))
% 0.61/0.83          | ~ (l1_pre_topc @ X68))),
% 0.61/0.83      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.61/0.83  thf('80', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.61/0.83        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['78', '79'])).
% 0.61/0.83  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('82', plain,
% 0.61/0.83      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.61/0.83        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['80', '81'])).
% 0.61/0.83  thf('83', plain,
% 0.61/0.83      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.61/0.83         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['77', '82'])).
% 0.61/0.83  thf('84', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['37', '56', '57'])).
% 0.61/0.83  thf('85', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.61/0.83  thf('86', plain,
% 0.61/0.83      (((k1_xboole_0)
% 0.61/0.83         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.83            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.61/0.83      inference('demod', [status(thm)], ['70', '85'])).
% 0.61/0.83  thf('87', plain,
% 0.61/0.83      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.61/0.83         = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['27', '60'])).
% 0.61/0.83  thf('88', plain,
% 0.61/0.83      (((k1_xboole_0)
% 0.61/0.83         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 0.61/0.83      inference('demod', [status(thm)], ['86', '87'])).
% 0.61/0.83  thf(t4_subset_1, axiom,
% 0.61/0.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.61/0.83  thf('89', plain,
% 0.61/0.83      (![X51 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X51))),
% 0.61/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.61/0.83  thf('90', plain,
% 0.61/0.83      (![X39 : $i, X40 : $i]:
% 0.61/0.83         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 0.61/0.83          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.61/0.83      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.61/0.83  thf('91', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['89', '90'])).
% 0.61/0.83  thf(t3_boole, axiom,
% 0.61/0.83    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.83  thf('92', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.61/0.83      inference('cnf', [status(esa)], [t3_boole])).
% 0.61/0.83  thf('93', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['91', '92'])).
% 0.61/0.83  thf('94', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['64', '88', '93'])).
% 0.61/0.83  thf('95', plain,
% 0.61/0.83      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))) = (sk_B))),
% 0.61/0.83      inference('demod', [status(thm)], ['11', '94'])).
% 0.61/0.83  thf('96', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(d2_tops_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( k2_tops_1 @ A @ B ) =
% 0.61/0.83             ( k9_subset_1 @
% 0.61/0.83               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.61/0.83               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.61/0.83  thf('97', plain,
% 0.61/0.83      (![X63 : $i, X64 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 0.61/0.83          | ((k2_tops_1 @ X64 @ X63)
% 0.61/0.83              = (k9_subset_1 @ (u1_struct_0 @ X64) @ 
% 0.61/0.83                 (k2_pre_topc @ X64 @ X63) @ 
% 0.61/0.83                 (k2_pre_topc @ X64 @ (k3_subset_1 @ (u1_struct_0 @ X64) @ X63))))
% 0.61/0.83          | ~ (l1_pre_topc @ X64))),
% 0.61/0.83      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.61/0.83  thf('98', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.61/0.83            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.61/0.83               (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.61/0.83               (k2_pre_topc @ sk_A @ 
% 0.61/0.83                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['96', '97'])).
% 0.61/0.83  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('100', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t52_pre_topc, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( l1_pre_topc @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.83           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.61/0.83             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.61/0.83               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.61/0.83  thf('101', plain,
% 0.61/0.83      (![X59 : $i, X60 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 0.61/0.83          | ~ (v4_pre_topc @ X59 @ X60)
% 0.61/0.83          | ((k2_pre_topc @ X60 @ X59) = (X59))
% 0.61/0.83          | ~ (l1_pre_topc @ X60))),
% 0.61/0.83      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.61/0.83  thf('102', plain,
% 0.61/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.83        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.61/0.83        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['100', '101'])).
% 0.61/0.83  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('104', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('105', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.61/0.83      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.61/0.83  thf('106', plain,
% 0.61/0.83      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.61/0.83         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.61/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf('107', plain,
% 0.61/0.83      (((k2_tops_1 @ sk_A @ sk_B)
% 0.61/0.83         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.61/0.83            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.61/0.83      inference('demod', [status(thm)], ['98', '99', '105', '106'])).
% 0.61/0.83  thf('108', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['64', '88', '93'])).
% 0.61/0.83  thf('109', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['64', '88', '93'])).
% 0.61/0.83  thf('110', plain,
% 0.61/0.83      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.61/0.83         = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['27', '60'])).
% 0.61/0.83  thf('111', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['64', '88', '93'])).
% 0.61/0.83  thf('112', plain,
% 0.61/0.83      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.61/0.83         = (k2_struct_0 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['110', '111'])).
% 0.61/0.83  thf('113', plain,
% 0.61/0.83      (![X51 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X51))),
% 0.61/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.61/0.83  thf('114', plain,
% 0.61/0.83      (![X41 : $i, X42 : $i]:
% 0.61/0.83         ((m1_subset_1 @ (k3_subset_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))
% 0.61/0.83          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.61/0.83      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.61/0.83  thf('115', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['113', '114'])).
% 0.61/0.83  thf('116', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['91', '92'])).
% 0.61/0.83  thf('117', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['115', '116'])).
% 0.61/0.83  thf(redefinition_k9_subset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.83       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.61/0.83  thf('118', plain,
% 0.61/0.83      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.61/0.83         (((k9_subset_1 @ X50 @ X48 @ X49) = (k3_xboole_0 @ X48 @ X49))
% 0.61/0.83          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 0.61/0.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.61/0.83  thf('119', plain,
% 0.61/0.83      (![X52 : $i, X53 : $i]:
% 0.61/0.83         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.61/0.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.61/0.83  thf('120', plain,
% 0.61/0.83      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.61/0.83         (((k9_subset_1 @ X50 @ X48 @ X49)
% 0.61/0.83            = (k1_setfam_1 @ (k2_tarski @ X48 @ X49)))
% 0.61/0.83          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 0.61/0.83      inference('demod', [status(thm)], ['118', '119'])).
% 0.61/0.83  thf('121', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['117', '120'])).
% 0.61/0.83  thf('122', plain,
% 0.61/0.83      (((k2_tops_1 @ sk_A @ sk_B)
% 0.61/0.83         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))))),
% 0.61/0.83      inference('demod', [status(thm)], ['107', '108', '109', '112', '121'])).
% 0.61/0.83  thf('123', plain, (((k2_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.61/0.83      inference('sup+', [status(thm)], ['95', '122'])).
% 0.61/0.83  thf('124', plain,
% 0.61/0.83      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.61/0.83         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.61/0.83      inference('split', [status(esa)], ['36'])).
% 0.61/0.83  thf('125', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['37', '56'])).
% 0.61/0.83  thf('126', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['124', '125'])).
% 0.61/0.83  thf('127', plain, ($false),
% 0.61/0.83      inference('simplify_reflect-', [status(thm)], ['123', '126'])).
% 0.61/0.83  
% 0.61/0.83  % SZS output end Refutation
% 0.61/0.83  
% 0.61/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
