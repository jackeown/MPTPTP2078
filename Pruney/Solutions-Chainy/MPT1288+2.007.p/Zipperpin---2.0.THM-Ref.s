%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K2iKrHALb0

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:58 EST 2020

% Result     : Theorem 4.35s
% Output     : Refutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 252 expanded)
%              Number of leaves         :   32 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          : 1247 (3193 expanded)
%              Number of equality atoms :   36 ( 126 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t110_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t110_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ ( k2_tops_1 @ X22 @ ( k2_tops_1 @ X22 @ X21 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('2',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t94_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_tops_1 @ X28 @ X29 )
      | ( X28
        = ( k2_tops_1 @ X29 @ X28 ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('17',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t96_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X31 @ X30 ) @ X31 )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t96_tops_1])).

thf('28',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('33',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['33','38','39','40'])).

thf('42',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['28','29','30','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('48',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','60'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_tops_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ ( k1_tops_1 @ X23 @ X24 ) )
        = ( k1_tops_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','87'])).

thf('89',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['42','95'])).

thf('97',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','96'])).

thf('98',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','97'])).

thf('99',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K2iKrHALb0
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.35/4.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.35/4.57  % Solved by: fo/fo7.sh
% 4.35/4.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.35/4.57  % done 4928 iterations in 4.119s
% 4.35/4.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.35/4.57  % SZS output start Refutation
% 4.35/4.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.35/4.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 4.35/4.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.35/4.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.35/4.57  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 4.35/4.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.35/4.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.35/4.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.35/4.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.35/4.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 4.35/4.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.35/4.57  thf(sk_A_type, type, sk_A: $i).
% 4.35/4.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 4.35/4.57  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 4.35/4.57  thf(sk_B_type, type, sk_B: $i).
% 4.35/4.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.35/4.57  thf(t110_tops_1, conjecture,
% 4.35/4.57    (![A:$i]:
% 4.35/4.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.35/4.57       ( ![B:$i]:
% 4.35/4.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57           ( ( v4_tops_1 @ B @ A ) =>
% 4.35/4.57             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 4.35/4.57  thf(zf_stmt_0, negated_conjecture,
% 4.35/4.57    (~( ![A:$i]:
% 4.35/4.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.35/4.57          ( ![B:$i]:
% 4.35/4.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57              ( ( v4_tops_1 @ B @ A ) =>
% 4.35/4.57                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 4.35/4.57    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 4.35/4.57  thf('0', plain,
% 4.35/4.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf(l80_tops_1, axiom,
% 4.35/4.57    (![A:$i]:
% 4.35/4.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.35/4.57       ( ![B:$i]:
% 4.35/4.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 4.35/4.57             ( k1_xboole_0 ) ) ) ) ))).
% 4.35/4.57  thf('1', plain,
% 4.35/4.57      (![X21 : $i, X22 : $i]:
% 4.35/4.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.35/4.57          | ((k1_tops_1 @ X22 @ (k2_tops_1 @ X22 @ (k2_tops_1 @ X22 @ X21)))
% 4.35/4.57              = (k1_xboole_0))
% 4.35/4.57          | ~ (l1_pre_topc @ X22)
% 4.35/4.57          | ~ (v2_pre_topc @ X22))),
% 4.35/4.57      inference('cnf', [status(esa)], [l80_tops_1])).
% 4.35/4.57  thf('2', plain,
% 4.35/4.57      ((~ (v2_pre_topc @ sk_A)
% 4.35/4.57        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.57        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 4.35/4.57            = (k1_xboole_0)))),
% 4.35/4.57      inference('sup-', [status(thm)], ['0', '1'])).
% 4.35/4.57  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('5', plain,
% 4.35/4.57      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 4.35/4.57         = (k1_xboole_0))),
% 4.35/4.57      inference('demod', [status(thm)], ['2', '3', '4'])).
% 4.35/4.57  thf('6', plain,
% 4.35/4.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf(dt_k2_tops_1, axiom,
% 4.35/4.57    (![A:$i,B:$i]:
% 4.35/4.57     ( ( ( l1_pre_topc @ A ) & 
% 4.35/4.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.35/4.57       ( m1_subset_1 @
% 4.35/4.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.35/4.57  thf('7', plain,
% 4.35/4.57      (![X13 : $i, X14 : $i]:
% 4.35/4.57         (~ (l1_pre_topc @ X13)
% 4.35/4.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 4.35/4.57          | (m1_subset_1 @ (k2_tops_1 @ X13 @ X14) @ 
% 4.35/4.57             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 4.35/4.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 4.35/4.57  thf('8', plain,
% 4.35/4.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 4.35/4.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.57        | ~ (l1_pre_topc @ sk_A))),
% 4.35/4.57      inference('sup-', [status(thm)], ['6', '7'])).
% 4.35/4.57  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('10', plain,
% 4.35/4.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 4.35/4.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('demod', [status(thm)], ['8', '9'])).
% 4.35/4.57  thf(t94_tops_1, axiom,
% 4.35/4.57    (![A:$i]:
% 4.35/4.57     ( ( l1_pre_topc @ A ) =>
% 4.35/4.57       ( ![B:$i]:
% 4.35/4.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57           ( ( v4_pre_topc @ B @ A ) =>
% 4.35/4.57             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 4.35/4.57  thf('11', plain,
% 4.35/4.57      (![X28 : $i, X29 : $i]:
% 4.35/4.57         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 4.35/4.57          | ~ (v3_tops_1 @ X28 @ X29)
% 4.35/4.57          | ((X28) = (k2_tops_1 @ X29 @ X28))
% 4.35/4.57          | ~ (v4_pre_topc @ X28 @ X29)
% 4.35/4.57          | ~ (l1_pre_topc @ X29))),
% 4.35/4.57      inference('cnf', [status(esa)], [t94_tops_1])).
% 4.35/4.57  thf('12', plain,
% 4.35/4.57      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.57        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.35/4.57        | ((k2_tops_1 @ sk_A @ sk_B)
% 4.35/4.57            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 4.35/4.57        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 4.35/4.57      inference('sup-', [status(thm)], ['10', '11'])).
% 4.35/4.57  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('14', plain,
% 4.35/4.57      ((~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.35/4.57        | ((k2_tops_1 @ sk_A @ sk_B)
% 4.35/4.57            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 4.35/4.57        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 4.35/4.57      inference('demod', [status(thm)], ['12', '13'])).
% 4.35/4.57  thf('15', plain,
% 4.35/4.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf(fc11_tops_1, axiom,
% 4.35/4.57    (![A:$i,B:$i]:
% 4.35/4.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.35/4.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.35/4.57       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 4.35/4.57  thf('16', plain,
% 4.35/4.57      (![X15 : $i, X16 : $i]:
% 4.35/4.57         (~ (l1_pre_topc @ X15)
% 4.35/4.57          | ~ (v2_pre_topc @ X15)
% 4.35/4.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.35/4.57          | (v4_pre_topc @ (k2_tops_1 @ X15 @ X16) @ X15))),
% 4.35/4.57      inference('cnf', [status(esa)], [fc11_tops_1])).
% 4.35/4.57  thf('17', plain,
% 4.35/4.57      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.35/4.57        | ~ (v2_pre_topc @ sk_A)
% 4.35/4.57        | ~ (l1_pre_topc @ sk_A))),
% 4.35/4.57      inference('sup-', [status(thm)], ['15', '16'])).
% 4.35/4.57  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('20', plain, ((v4_pre_topc @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 4.35/4.57      inference('demod', [status(thm)], ['17', '18', '19'])).
% 4.35/4.57  thf('21', plain,
% 4.35/4.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.35/4.57          = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 4.35/4.57        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 4.35/4.57      inference('demod', [status(thm)], ['14', '20'])).
% 4.35/4.57  thf('22', plain,
% 4.35/4.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf(dt_k2_pre_topc, axiom,
% 4.35/4.57    (![A:$i,B:$i]:
% 4.35/4.57     ( ( ( l1_pre_topc @ A ) & 
% 4.35/4.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.35/4.57       ( m1_subset_1 @
% 4.35/4.57         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.35/4.57  thf('23', plain,
% 4.35/4.57      (![X3 : $i, X4 : $i]:
% 4.35/4.57         (~ (l1_pre_topc @ X3)
% 4.35/4.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 4.35/4.57          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 4.35/4.57             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 4.35/4.57      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 4.35/4.57  thf('24', plain,
% 4.35/4.57      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.57        | ~ (l1_pre_topc @ sk_A))),
% 4.35/4.57      inference('sup-', [status(thm)], ['22', '23'])).
% 4.35/4.57  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('26', plain,
% 4.35/4.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('demod', [status(thm)], ['24', '25'])).
% 4.35/4.57  thf(t96_tops_1, axiom,
% 4.35/4.57    (![A:$i]:
% 4.35/4.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.35/4.57       ( ![B:$i]:
% 4.35/4.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57           ( ( v4_pre_topc @ B @ A ) =>
% 4.35/4.57             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 4.35/4.57  thf('27', plain,
% 4.35/4.57      (![X30 : $i, X31 : $i]:
% 4.35/4.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 4.35/4.57          | (v3_tops_1 @ (k2_tops_1 @ X31 @ X30) @ X31)
% 4.35/4.57          | ~ (v4_pre_topc @ X30 @ X31)
% 4.35/4.57          | ~ (l1_pre_topc @ X31)
% 4.35/4.57          | ~ (v2_pre_topc @ X31))),
% 4.35/4.57      inference('cnf', [status(esa)], [t96_tops_1])).
% 4.35/4.57  thf('28', plain,
% 4.35/4.57      ((~ (v2_pre_topc @ sk_A)
% 4.35/4.57        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.57        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 4.35/4.57        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A))),
% 4.35/4.57      inference('sup-', [status(thm)], ['26', '27'])).
% 4.35/4.57  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('31', plain,
% 4.35/4.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('demod', [status(thm)], ['24', '25'])).
% 4.35/4.57  thf(fc1_tops_1, axiom,
% 4.35/4.57    (![A:$i,B:$i]:
% 4.35/4.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.35/4.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.35/4.57       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 4.35/4.57  thf('32', plain,
% 4.35/4.57      (![X17 : $i, X18 : $i]:
% 4.35/4.57         (~ (l1_pre_topc @ X17)
% 4.35/4.57          | ~ (v2_pre_topc @ X17)
% 4.35/4.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 4.35/4.57          | (v4_pre_topc @ (k2_pre_topc @ X17 @ X18) @ X17))),
% 4.35/4.57      inference('cnf', [status(esa)], [fc1_tops_1])).
% 4.35/4.57  thf('33', plain,
% 4.35/4.57      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.57         sk_A)
% 4.35/4.57        | ~ (v2_pre_topc @ sk_A)
% 4.35/4.57        | ~ (l1_pre_topc @ sk_A))),
% 4.35/4.57      inference('sup-', [status(thm)], ['31', '32'])).
% 4.35/4.57  thf('34', plain,
% 4.35/4.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf(projectivity_k2_pre_topc, axiom,
% 4.35/4.57    (![A:$i,B:$i]:
% 4.35/4.57     ( ( ( l1_pre_topc @ A ) & 
% 4.35/4.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.35/4.57       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 4.35/4.57         ( k2_pre_topc @ A @ B ) ) ))).
% 4.35/4.57  thf('35', plain,
% 4.35/4.57      (![X5 : $i, X6 : $i]:
% 4.35/4.57         (~ (l1_pre_topc @ X5)
% 4.35/4.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 4.35/4.57          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 4.35/4.57              = (k2_pre_topc @ X5 @ X6)))),
% 4.35/4.57      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 4.35/4.57  thf('36', plain,
% 4.35/4.57      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.57          = (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.57        | ~ (l1_pre_topc @ sk_A))),
% 4.35/4.57      inference('sup-', [status(thm)], ['34', '35'])).
% 4.35/4.57  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('38', plain,
% 4.35/4.57      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.57         = (k2_pre_topc @ sk_A @ sk_B))),
% 4.35/4.57      inference('demod', [status(thm)], ['36', '37'])).
% 4.35/4.57  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('41', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 4.35/4.57      inference('demod', [status(thm)], ['33', '38', '39', '40'])).
% 4.35/4.57  thf('42', plain,
% 4.35/4.57      ((v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)),
% 4.35/4.57      inference('demod', [status(thm)], ['28', '29', '30', '41'])).
% 4.35/4.57  thf('43', plain,
% 4.35/4.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('demod', [status(thm)], ['24', '25'])).
% 4.35/4.57  thf(l78_tops_1, axiom,
% 4.35/4.57    (![A:$i]:
% 4.35/4.57     ( ( l1_pre_topc @ A ) =>
% 4.35/4.57       ( ![B:$i]:
% 4.35/4.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57           ( ( k2_tops_1 @ A @ B ) =
% 4.35/4.57             ( k7_subset_1 @
% 4.35/4.57               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 4.35/4.57               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.35/4.57  thf('44', plain,
% 4.35/4.57      (![X19 : $i, X20 : $i]:
% 4.35/4.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 4.35/4.57          | ((k2_tops_1 @ X20 @ X19)
% 4.35/4.57              = (k7_subset_1 @ (u1_struct_0 @ X20) @ 
% 4.35/4.57                 (k2_pre_topc @ X20 @ X19) @ (k1_tops_1 @ X20 @ X19)))
% 4.35/4.57          | ~ (l1_pre_topc @ X20))),
% 4.35/4.57      inference('cnf', [status(esa)], [l78_tops_1])).
% 4.35/4.57  thf('45', plain,
% 4.35/4.57      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.57        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.35/4.57               (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.57               (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 4.35/4.57      inference('sup-', [status(thm)], ['43', '44'])).
% 4.35/4.57  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf('47', plain,
% 4.35/4.57      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.57         = (k2_pre_topc @ sk_A @ sk_B))),
% 4.35/4.57      inference('demod', [status(thm)], ['36', '37'])).
% 4.35/4.57  thf('48', plain,
% 4.35/4.57      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.57         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.57            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 4.35/4.57      inference('demod', [status(thm)], ['45', '46', '47'])).
% 4.35/4.57  thf('49', plain,
% 4.35/4.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('demod', [status(thm)], ['24', '25'])).
% 4.35/4.57  thf('50', plain,
% 4.35/4.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.57  thf(t48_tops_1, axiom,
% 4.35/4.57    (![A:$i]:
% 4.35/4.57     ( ( l1_pre_topc @ A ) =>
% 4.35/4.57       ( ![B:$i]:
% 4.35/4.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57           ( ![C:$i]:
% 4.35/4.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.57               ( ( r1_tarski @ B @ C ) =>
% 4.35/4.57                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 4.35/4.57  thf('51', plain,
% 4.35/4.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.35/4.57         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.35/4.57          | ~ (r1_tarski @ X25 @ X27)
% 4.35/4.57          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ (k1_tops_1 @ X26 @ X27))
% 4.35/4.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.35/4.58          | ~ (l1_pre_topc @ X26))),
% 4.35/4.58      inference('cnf', [status(esa)], [t48_tops_1])).
% 4.35/4.58  thf('52', plain,
% 4.35/4.58      (![X0 : $i]:
% 4.35/4.58         (~ (l1_pre_topc @ sk_A)
% 4.35/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.58          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 4.35/4.58          | ~ (r1_tarski @ sk_B @ X0))),
% 4.35/4.58      inference('sup-', [status(thm)], ['50', '51'])).
% 4.35/4.58  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('54', plain,
% 4.35/4.58      (![X0 : $i]:
% 4.35/4.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.58          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 4.35/4.58          | ~ (r1_tarski @ sk_B @ X0))),
% 4.35/4.58      inference('demod', [status(thm)], ['52', '53'])).
% 4.35/4.58  thf('55', plain,
% 4.35/4.58      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.58        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.35/4.58           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 4.35/4.58      inference('sup-', [status(thm)], ['49', '54'])).
% 4.35/4.58  thf('56', plain,
% 4.35/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf(t48_pre_topc, axiom,
% 4.35/4.58    (![A:$i]:
% 4.35/4.58     ( ( l1_pre_topc @ A ) =>
% 4.35/4.58       ( ![B:$i]:
% 4.35/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.58           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 4.35/4.58  thf('57', plain,
% 4.35/4.58      (![X7 : $i, X8 : $i]:
% 4.35/4.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 4.35/4.58          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 4.35/4.58          | ~ (l1_pre_topc @ X8))),
% 4.35/4.58      inference('cnf', [status(esa)], [t48_pre_topc])).
% 4.35/4.58  thf('58', plain,
% 4.35/4.58      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.58        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.35/4.58      inference('sup-', [status(thm)], ['56', '57'])).
% 4.35/4.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('60', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 4.35/4.58      inference('demod', [status(thm)], ['58', '59'])).
% 4.35/4.58  thf('61', plain,
% 4.35/4.58      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.35/4.58        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.35/4.58      inference('demod', [status(thm)], ['55', '60'])).
% 4.35/4.58  thf(d10_xboole_0, axiom,
% 4.35/4.58    (![A:$i,B:$i]:
% 4.35/4.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.35/4.58  thf('62', plain,
% 4.35/4.58      (![X0 : $i, X2 : $i]:
% 4.35/4.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.35/4.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.35/4.58  thf('63', plain,
% 4.35/4.58      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58           (k1_tops_1 @ sk_A @ sk_B))
% 4.35/4.58        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.58            = (k1_tops_1 @ sk_A @ sk_B)))),
% 4.35/4.58      inference('sup-', [status(thm)], ['61', '62'])).
% 4.35/4.58  thf('64', plain,
% 4.35/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf(d6_tops_1, axiom,
% 4.35/4.58    (![A:$i]:
% 4.35/4.58     ( ( l1_pre_topc @ A ) =>
% 4.35/4.58       ( ![B:$i]:
% 4.35/4.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.58           ( ( v4_tops_1 @ B @ A ) <=>
% 4.35/4.58             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 4.35/4.58               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 4.35/4.58  thf('65', plain,
% 4.35/4.58      (![X9 : $i, X10 : $i]:
% 4.35/4.58         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 4.35/4.58          | ~ (v4_tops_1 @ X9 @ X10)
% 4.35/4.58          | (r1_tarski @ (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)) @ X9)
% 4.35/4.58          | ~ (l1_pre_topc @ X10))),
% 4.35/4.58      inference('cnf', [status(esa)], [d6_tops_1])).
% 4.35/4.58  thf('66', plain,
% 4.35/4.58      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.58        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 4.35/4.58        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 4.35/4.58      inference('sup-', [status(thm)], ['64', '65'])).
% 4.35/4.58  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('68', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('69', plain,
% 4.35/4.58      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 4.35/4.58      inference('demod', [status(thm)], ['66', '67', '68'])).
% 4.35/4.58  thf('70', plain,
% 4.35/4.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.58      inference('demod', [status(thm)], ['24', '25'])).
% 4.35/4.58  thf(dt_k1_tops_1, axiom,
% 4.35/4.58    (![A:$i,B:$i]:
% 4.35/4.58     ( ( ( l1_pre_topc @ A ) & 
% 4.35/4.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.35/4.58       ( m1_subset_1 @
% 4.35/4.58         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.35/4.58  thf('71', plain,
% 4.35/4.58      (![X11 : $i, X12 : $i]:
% 4.35/4.58         (~ (l1_pre_topc @ X11)
% 4.35/4.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 4.35/4.58          | (m1_subset_1 @ (k1_tops_1 @ X11 @ X12) @ 
% 4.35/4.58             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 4.35/4.58      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 4.35/4.58  thf('72', plain,
% 4.35/4.58      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.58        | ~ (l1_pre_topc @ sk_A))),
% 4.35/4.58      inference('sup-', [status(thm)], ['70', '71'])).
% 4.35/4.58  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('74', plain,
% 4.35/4.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.58      inference('demod', [status(thm)], ['72', '73'])).
% 4.35/4.58  thf('75', plain,
% 4.35/4.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.35/4.58         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.35/4.58          | ~ (r1_tarski @ X25 @ X27)
% 4.35/4.58          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ (k1_tops_1 @ X26 @ X27))
% 4.35/4.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.35/4.58          | ~ (l1_pre_topc @ X26))),
% 4.35/4.58      inference('cnf', [status(esa)], [t48_tops_1])).
% 4.35/4.58  thf('76', plain,
% 4.35/4.58      (![X0 : $i]:
% 4.35/4.58         (~ (l1_pre_topc @ sk_A)
% 4.35/4.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.58          | (r1_tarski @ 
% 4.35/4.58             (k1_tops_1 @ sk_A @ 
% 4.35/4.58              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 4.35/4.58             (k1_tops_1 @ sk_A @ X0))
% 4.35/4.58          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58               X0))),
% 4.35/4.58      inference('sup-', [status(thm)], ['74', '75'])).
% 4.35/4.58  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('78', plain,
% 4.35/4.58      (![X0 : $i]:
% 4.35/4.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.58          | (r1_tarski @ 
% 4.35/4.58             (k1_tops_1 @ sk_A @ 
% 4.35/4.58              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 4.35/4.58             (k1_tops_1 @ sk_A @ X0))
% 4.35/4.58          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58               X0))),
% 4.35/4.58      inference('demod', [status(thm)], ['76', '77'])).
% 4.35/4.58  thf('79', plain,
% 4.35/4.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.58      inference('demod', [status(thm)], ['24', '25'])).
% 4.35/4.58  thf(projectivity_k1_tops_1, axiom,
% 4.35/4.58    (![A:$i,B:$i]:
% 4.35/4.58     ( ( ( l1_pre_topc @ A ) & 
% 4.35/4.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.35/4.58       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 4.35/4.58  thf('80', plain,
% 4.35/4.58      (![X23 : $i, X24 : $i]:
% 4.35/4.58         (~ (l1_pre_topc @ X23)
% 4.35/4.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 4.35/4.58          | ((k1_tops_1 @ X23 @ (k1_tops_1 @ X23 @ X24))
% 4.35/4.58              = (k1_tops_1 @ X23 @ X24)))),
% 4.35/4.58      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 4.35/4.58  thf('81', plain,
% 4.35/4.58      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 4.35/4.58          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 4.35/4.58        | ~ (l1_pre_topc @ sk_A))),
% 4.35/4.58      inference('sup-', [status(thm)], ['79', '80'])).
% 4.35/4.58  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('83', plain,
% 4.35/4.58      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 4.35/4.58         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.35/4.58      inference('demod', [status(thm)], ['81', '82'])).
% 4.35/4.58  thf('84', plain,
% 4.35/4.58      (![X0 : $i]:
% 4.35/4.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.58          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58             (k1_tops_1 @ sk_A @ X0))
% 4.35/4.58          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58               X0))),
% 4.35/4.58      inference('demod', [status(thm)], ['78', '83'])).
% 4.35/4.58  thf('85', plain,
% 4.35/4.58      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58         (k1_tops_1 @ sk_A @ sk_B))
% 4.35/4.58        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.35/4.58      inference('sup-', [status(thm)], ['69', '84'])).
% 4.35/4.58  thf('86', plain,
% 4.35/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('87', plain,
% 4.35/4.58      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 4.35/4.58        (k1_tops_1 @ sk_A @ sk_B))),
% 4.35/4.58      inference('demod', [status(thm)], ['85', '86'])).
% 4.35/4.58  thf('88', plain,
% 4.35/4.58      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.58         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.35/4.58      inference('demod', [status(thm)], ['63', '87'])).
% 4.35/4.58  thf('89', plain,
% 4.35/4.58      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 4.35/4.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.35/4.58      inference('demod', [status(thm)], ['48', '88'])).
% 4.35/4.58  thf('90', plain,
% 4.35/4.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('91', plain,
% 4.35/4.58      (![X19 : $i, X20 : $i]:
% 4.35/4.58         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 4.35/4.58          | ((k2_tops_1 @ X20 @ X19)
% 4.35/4.58              = (k7_subset_1 @ (u1_struct_0 @ X20) @ 
% 4.35/4.58                 (k2_pre_topc @ X20 @ X19) @ (k1_tops_1 @ X20 @ X19)))
% 4.35/4.58          | ~ (l1_pre_topc @ X20))),
% 4.35/4.58      inference('cnf', [status(esa)], [l78_tops_1])).
% 4.35/4.58  thf('92', plain,
% 4.35/4.58      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.58        | ((k2_tops_1 @ sk_A @ sk_B)
% 4.35/4.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.35/4.58               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.35/4.58      inference('sup-', [status(thm)], ['90', '91'])).
% 4.35/4.58  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('94', plain,
% 4.35/4.58      (((k2_tops_1 @ sk_A @ sk_B)
% 4.35/4.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.35/4.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.35/4.58      inference('demod', [status(thm)], ['92', '93'])).
% 4.35/4.58  thf('95', plain,
% 4.35/4.58      (((k2_tops_1 @ sk_A @ sk_B)
% 4.35/4.58         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.35/4.58      inference('sup+', [status(thm)], ['89', '94'])).
% 4.35/4.58  thf('96', plain, ((v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 4.35/4.58      inference('demod', [status(thm)], ['42', '95'])).
% 4.35/4.58  thf('97', plain,
% 4.35/4.58      (((k2_tops_1 @ sk_A @ sk_B)
% 4.35/4.58         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.35/4.58      inference('demod', [status(thm)], ['21', '96'])).
% 4.35/4.58  thf('98', plain,
% 4.35/4.58      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 4.35/4.58      inference('demod', [status(thm)], ['5', '97'])).
% 4.35/4.58  thf('99', plain,
% 4.35/4.58      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 4.35/4.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.58  thf('100', plain, ($false),
% 4.35/4.58      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 4.35/4.58  
% 4.35/4.58  % SZS output end Refutation
% 4.35/4.58  
% 4.35/4.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
