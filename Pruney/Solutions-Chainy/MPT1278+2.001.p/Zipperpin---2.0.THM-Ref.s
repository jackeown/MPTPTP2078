%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zfCJwJYFpE

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:39 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 281 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          : 1019 (2458 expanded)
%              Number of equality atoms :   43 ( 122 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('5',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v1_tops_1 @ X31 @ X32 )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k2_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) @ X34 )
      | ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('20',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) @ X36 )
      | ~ ( v3_tops_1 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(cc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_tops_1 @ X29 @ X30 )
      | ~ ( v1_xboole_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc3_tops_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_tops_1 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_tops_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) @ X36 )
      | ~ ( v3_tops_1 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X13 @ X14 ) @ X14 )
      | ( X14
        = ( k2_subset_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X13 @ X14 ) @ X14 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('62',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['57','60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','64'])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','65'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('71',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v1_tops_1 @ X31 @ X32 )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k2_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('76',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('83',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) @ X34 )
      | ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['57','60','63'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('94',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('102',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['31','100','101'])).

thf('103',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zfCJwJYFpE
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.80/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.02  % Solved by: fo/fo7.sh
% 0.80/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.02  % done 582 iterations in 0.524s
% 0.80/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.02  % SZS output start Refutation
% 0.80/1.02  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.80/1.02  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.80/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.02  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.80/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.02  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.80/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.80/1.02  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.80/1.02  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.80/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.02  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.80/1.02  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.80/1.02  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.80/1.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.80/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.80/1.02  thf(t97_tops_1, conjecture,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.80/1.02             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.80/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.02    (~( ![A:$i]:
% 0.80/1.02        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.02          ( ![B:$i]:
% 0.80/1.02            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.80/1.02                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.80/1.02    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.80/1.02  thf('0', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(involutiveness_k3_subset_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.02       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.80/1.02  thf('1', plain,
% 0.80/1.02      (![X11 : $i, X12 : $i]:
% 0.80/1.02         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.80/1.02          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.80/1.02      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.80/1.02  thf('2', plain,
% 0.80/1.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.02         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.80/1.02      inference('sup-', [status(thm)], ['0', '1'])).
% 0.80/1.02  thf('3', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(dt_k3_subset_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.02       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.80/1.02  thf('4', plain,
% 0.80/1.02      (![X9 : $i, X10 : $i]:
% 0.80/1.02         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.80/1.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.80/1.02      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.80/1.02  thf('5', plain,
% 0.80/1.02      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.80/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['3', '4'])).
% 0.80/1.02  thf(d3_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( v1_tops_1 @ B @ A ) <=>
% 0.80/1.02             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.80/1.02  thf('6', plain,
% 0.80/1.02      (![X31 : $i, X32 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.02          | ~ (v1_tops_1 @ X31 @ X32)
% 0.80/1.02          | ((k2_pre_topc @ X32 @ X31) = (k2_struct_0 @ X32))
% 0.80/1.02          | ~ (l1_pre_topc @ X32))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.80/1.02  thf('7', plain,
% 0.80/1.02      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.02        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.80/1.02            = (k2_struct_0 @ sk_A))
% 0.80/1.02        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['5', '6'])).
% 0.80/1.02  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('9', plain,
% 0.80/1.02      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.80/1.02          = (k2_struct_0 @ sk_A))
% 0.80/1.02        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/1.02  thf('10', plain,
% 0.80/1.02      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.80/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['3', '4'])).
% 0.80/1.02  thf(t52_pre_topc, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.80/1.02             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.80/1.02               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.80/1.02  thf('11', plain,
% 0.80/1.02      (![X25 : $i, X26 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.80/1.02          | ~ (v4_pre_topc @ X25 @ X26)
% 0.80/1.02          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 0.80/1.02          | ~ (l1_pre_topc @ X26))),
% 0.80/1.02      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.80/1.02  thf('12', plain,
% 0.80/1.02      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.02        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.80/1.02            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.80/1.02        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['10', '11'])).
% 0.80/1.02  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('14', plain,
% 0.80/1.02      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.80/1.02          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.80/1.02        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['12', '13'])).
% 0.80/1.02  thf('15', plain,
% 0.80/1.02      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.80/1.02        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['3', '4'])).
% 0.80/1.02  thf(t29_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( v4_pre_topc @ B @ A ) <=>
% 0.80/1.02             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.80/1.02  thf('16', plain,
% 0.80/1.02      (![X33 : $i, X34 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.80/1.02          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33) @ X34)
% 0.80/1.02          | (v4_pre_topc @ X33 @ X34)
% 0.80/1.02          | ~ (l1_pre_topc @ X34))),
% 0.80/1.02      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.80/1.02  thf('17', plain,
% 0.80/1.02      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.02        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.80/1.02        | ~ (v3_pre_topc @ 
% 0.80/1.02             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.02              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.80/1.02             sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['15', '16'])).
% 0.80/1.02  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('19', plain,
% 0.80/1.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.02         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.80/1.02      inference('sup-', [status(thm)], ['0', '1'])).
% 0.80/1.02  thf('20', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('21', plain,
% 0.80/1.02      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.80/1.02  thf('22', plain,
% 0.80/1.02      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.80/1.02         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.80/1.02      inference('demod', [status(thm)], ['14', '21'])).
% 0.80/1.02  thf('23', plain,
% 0.80/1.02      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))
% 0.80/1.02        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['9', '22'])).
% 0.80/1.02  thf('24', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(t91_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( v3_tops_1 @ B @ A ) =>
% 0.80/1.02             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.80/1.02  thf('25', plain,
% 0.80/1.02      (![X35 : $i, X36 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.80/1.02          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35) @ X36)
% 0.80/1.02          | ~ (v3_tops_1 @ X35 @ X36)
% 0.80/1.02          | ~ (l1_pre_topc @ X36))),
% 0.80/1.02      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.80/1.02  thf('26', plain,
% 0.80/1.02      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.02        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.80/1.02        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['24', '25'])).
% 0.80/1.02  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('28', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('29', plain,
% 0.80/1.02      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.80/1.02      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.80/1.02  thf('30', plain,
% 0.80/1.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['23', '29'])).
% 0.80/1.02  thf('31', plain,
% 0.80/1.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.80/1.02      inference('demod', [status(thm)], ['2', '30'])).
% 0.80/1.02  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(d3_tarski, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( r1_tarski @ A @ B ) <=>
% 0.80/1.02       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.80/1.02  thf('33', plain,
% 0.80/1.02      (![X1 : $i, X3 : $i]:
% 0.80/1.02         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_tarski])).
% 0.80/1.02  thf(dt_k2_subset_1, axiom,
% 0.80/1.02    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.80/1.02  thf('34', plain,
% 0.80/1.02      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.80/1.02      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.80/1.02  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.80/1.02  thf('35', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.80/1.02      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.80/1.02  thf('36', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.80/1.02      inference('demod', [status(thm)], ['34', '35'])).
% 0.80/1.02  thf(t5_subset, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.80/1.02          ( v1_xboole_0 @ C ) ) ))).
% 0.80/1.02  thf('37', plain,
% 0.80/1.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.80/1.02         (~ (r2_hidden @ X22 @ X23)
% 0.80/1.02          | ~ (v1_xboole_0 @ X24)
% 0.80/1.02          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t5_subset])).
% 0.80/1.02  thf('38', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['36', '37'])).
% 0.80/1.02  thf('39', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['33', '38'])).
% 0.80/1.02  thf(t3_subset, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.80/1.02  thf('40', plain,
% 0.80/1.02      (![X16 : $i, X18 : $i]:
% 0.80/1.02         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.80/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.02  thf('41', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['39', '40'])).
% 0.80/1.02  thf(cc3_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( v1_xboole_0 @ B ) => ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.80/1.02  thf('42', plain,
% 0.80/1.02      (![X29 : $i, X30 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.80/1.02          | (v3_tops_1 @ X29 @ X30)
% 0.80/1.02          | ~ (v1_xboole_0 @ X29)
% 0.80/1.02          | ~ (l1_pre_topc @ X30)
% 0.80/1.02          | ~ (v2_pre_topc @ X30))),
% 0.80/1.02      inference('cnf', [status(esa)], [cc3_tops_1])).
% 0.80/1.02  thf('43', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (v1_xboole_0 @ X1)
% 0.80/1.02          | ~ (v2_pre_topc @ X0)
% 0.80/1.02          | ~ (l1_pre_topc @ X0)
% 0.80/1.02          | ~ (v1_xboole_0 @ X1)
% 0.80/1.02          | (v3_tops_1 @ X1 @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['41', '42'])).
% 0.80/1.02  thf('44', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((v3_tops_1 @ X1 @ X0)
% 0.80/1.02          | ~ (l1_pre_topc @ X0)
% 0.80/1.02          | ~ (v2_pre_topc @ X0)
% 0.80/1.02          | ~ (v1_xboole_0 @ X1))),
% 0.80/1.02      inference('simplify', [status(thm)], ['43'])).
% 0.80/1.02  thf('45', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (v1_xboole_0 @ X0)
% 0.80/1.02          | ~ (v2_pre_topc @ sk_A)
% 0.80/1.02          | (v3_tops_1 @ X0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['32', '44'])).
% 0.80/1.02  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('47', plain,
% 0.80/1.02      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_tops_1 @ X0 @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['45', '46'])).
% 0.80/1.02  thf(t4_subset_1, axiom,
% 0.80/1.02    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.80/1.02  thf('48', plain,
% 0.80/1.02      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.02  thf('49', plain,
% 0.80/1.02      (![X35 : $i, X36 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.80/1.02          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35) @ X36)
% 0.80/1.02          | ~ (v3_tops_1 @ X35 @ X36)
% 0.80/1.02          | ~ (l1_pre_topc @ X36))),
% 0.80/1.02      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.80/1.02  thf('50', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ X0)
% 0.80/1.02          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.80/1.02          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['48', '49'])).
% 0.80/1.02  thf('51', plain,
% 0.80/1.02      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.02  thf('52', plain,
% 0.80/1.02      (![X11 : $i, X12 : $i]:
% 0.80/1.02         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.80/1.02          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.80/1.02      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.80/1.02  thf('53', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['51', '52'])).
% 0.80/1.02  thf(t39_subset_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.02       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.80/1.02         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.80/1.02  thf('54', plain,
% 0.80/1.02      (![X13 : $i, X14 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k3_subset_1 @ X13 @ X14) @ X14)
% 0.80/1.02          | ((X14) = (k2_subset_1 @ X13))
% 0.80/1.02          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t39_subset_1])).
% 0.80/1.02  thf('55', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.80/1.02      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.80/1.02  thf('56', plain,
% 0.80/1.02      (![X13 : $i, X14 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k3_subset_1 @ X13 @ X14) @ X14)
% 0.80/1.02          | ((X14) = (X13))
% 0.80/1.02          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.80/1.02      inference('demod', [status(thm)], ['54', '55'])).
% 0.80/1.02  thf('57', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.80/1.02          | ~ (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 0.80/1.02               (k1_zfmisc_1 @ X0))
% 0.80/1.02          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['53', '56'])).
% 0.80/1.02  thf('58', plain,
% 0.80/1.02      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.02  thf('59', plain,
% 0.80/1.02      (![X16 : $i, X17 : $i]:
% 0.80/1.02         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.02  thf('60', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.80/1.02      inference('sup-', [status(thm)], ['58', '59'])).
% 0.80/1.02  thf('61', plain,
% 0.80/1.02      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.02  thf('62', plain,
% 0.80/1.02      (![X9 : $i, X10 : $i]:
% 0.80/1.02         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.80/1.02          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.80/1.02      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.80/1.02  thf('63', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['61', '62'])).
% 0.80/1.02  thf('64', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.80/1.02      inference('demod', [status(thm)], ['57', '60', '63'])).
% 0.80/1.02  thf('65', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ X0)
% 0.80/1.02          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.80/1.02          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.80/1.02      inference('demod', [status(thm)], ['50', '64'])).
% 0.80/1.02  thf('66', plain,
% 0.80/1.02      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.80/1.02        | (v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.80/1.02        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['47', '65'])).
% 0.80/1.02  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.80/1.02  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.02      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.02  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('69', plain, ((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.80/1.02      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.80/1.02  thf('70', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.80/1.02      inference('demod', [status(thm)], ['34', '35'])).
% 0.80/1.02  thf('71', plain,
% 0.80/1.02      (![X31 : $i, X32 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.02          | ~ (v1_tops_1 @ X31 @ X32)
% 0.80/1.02          | ((k2_pre_topc @ X32 @ X31) = (k2_struct_0 @ X32))
% 0.80/1.02          | ~ (l1_pre_topc @ X32))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.80/1.02  thf('72', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ X0)
% 0.80/1.02          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.80/1.02          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['70', '71'])).
% 0.80/1.02  thf('73', plain,
% 0.80/1.02      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.80/1.02        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['69', '72'])).
% 0.80/1.02  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('75', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['39', '40'])).
% 0.80/1.02  thf(cc1_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.80/1.02  thf('76', plain,
% 0.80/1.02      (![X27 : $i, X28 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.80/1.02          | (v3_pre_topc @ X27 @ X28)
% 0.80/1.02          | ~ (v1_xboole_0 @ X27)
% 0.80/1.02          | ~ (l1_pre_topc @ X28)
% 0.80/1.02          | ~ (v2_pre_topc @ X28))),
% 0.80/1.02      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.80/1.02  thf('77', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (v1_xboole_0 @ X1)
% 0.80/1.02          | ~ (v2_pre_topc @ X0)
% 0.80/1.02          | ~ (l1_pre_topc @ X0)
% 0.80/1.02          | ~ (v1_xboole_0 @ X1)
% 0.80/1.02          | (v3_pre_topc @ X1 @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['75', '76'])).
% 0.80/1.02  thf('78', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((v3_pre_topc @ X1 @ X0)
% 0.80/1.02          | ~ (l1_pre_topc @ X0)
% 0.80/1.02          | ~ (v2_pre_topc @ X0)
% 0.80/1.02          | ~ (v1_xboole_0 @ X1))),
% 0.80/1.02      inference('simplify', [status(thm)], ['77'])).
% 0.80/1.02  thf('79', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (v1_xboole_0 @ X0)
% 0.80/1.02          | ~ (v2_pre_topc @ sk_A)
% 0.80/1.02          | (v3_pre_topc @ X0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['74', '78'])).
% 0.80/1.02  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('81', plain,
% 0.80/1.02      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['79', '80'])).
% 0.80/1.02  thf('82', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.80/1.02      inference('demod', [status(thm)], ['34', '35'])).
% 0.80/1.02  thf('83', plain,
% 0.80/1.02      (![X33 : $i, X34 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.80/1.02          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33) @ X34)
% 0.80/1.02          | (v4_pre_topc @ X33 @ X34)
% 0.80/1.02          | ~ (l1_pre_topc @ X34))),
% 0.80/1.02      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.80/1.02  thf('84', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ X0)
% 0.80/1.02          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.80/1.02          | ~ (v3_pre_topc @ 
% 0.80/1.02               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['82', '83'])).
% 0.80/1.02  thf('85', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['51', '52'])).
% 0.80/1.02  thf('86', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.80/1.02      inference('demod', [status(thm)], ['57', '60', '63'])).
% 0.80/1.02  thf('87', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.02      inference('demod', [status(thm)], ['85', '86'])).
% 0.80/1.02  thf('88', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ X0)
% 0.80/1.02          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.80/1.02          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.80/1.02      inference('demod', [status(thm)], ['84', '87'])).
% 0.80/1.02  thf('89', plain,
% 0.80/1.02      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.80/1.02        | (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.80/1.02        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['81', '88'])).
% 0.80/1.02  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.80/1.02      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.80/1.02  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('92', plain, ((v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.80/1.02      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.80/1.02  thf('93', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.80/1.02      inference('demod', [status(thm)], ['34', '35'])).
% 0.80/1.02  thf('94', plain,
% 0.80/1.02      (![X25 : $i, X26 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.80/1.02          | ~ (v4_pre_topc @ X25 @ X26)
% 0.80/1.02          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 0.80/1.02          | ~ (l1_pre_topc @ X26))),
% 0.80/1.02      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.80/1.02  thf('95', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (l1_pre_topc @ X0)
% 0.80/1.02          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.80/1.02          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['93', '94'])).
% 0.80/1.02  thf('96', plain,
% 0.80/1.02      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.80/1.02        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['92', '95'])).
% 0.80/1.02  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('98', plain,
% 0.80/1.02      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['96', '97'])).
% 0.80/1.02  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('100', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['73', '98', '99'])).
% 0.80/1.02  thf('101', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.02      inference('demod', [status(thm)], ['85', '86'])).
% 0.80/1.02  thf('102', plain, (((k1_xboole_0) = (sk_B))),
% 0.80/1.02      inference('demod', [status(thm)], ['31', '100', '101'])).
% 0.80/1.02  thf('103', plain, (((sk_B) != (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('104', plain, ($false),
% 0.80/1.02      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 0.80/1.02  
% 0.80/1.02  % SZS output end Refutation
% 0.80/1.02  
% 0.80/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
