%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1dvHZITXU

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:43 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 223 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  828 (2585 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('4',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( ( k2_struct_0 @ A )
                    = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  & ( r1_xboole_0 @ B @ C ) )
               => ( C
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( ( k2_struct_0 @ X55 )
       != ( k4_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 @ X56 ) )
      | ~ ( r1_xboole_0 @ X54 @ X56 )
      | ( X56
        = ( k7_subset_1 @ ( u1_struct_0 @ X55 ) @ ( k2_struct_0 @ X55 ) @ X54 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( l1_struct_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t25_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k2_struct_0 @ sk_A )
       != ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X46: $i] :
      ( ( l1_struct_0 @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X0
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k2_struct_0 @ sk_A )
       != ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k3_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 ) )
        = ( k2_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('15',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('17',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X21 @ ( k3_subset_1 @ X20 @ X19 ) )
      | ( r1_xboole_0 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_B_1 )
    | ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( r1_tarski @ X25 @ X23 )
      | ( r2_hidden @ ( sk_D @ X23 @ X25 @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ ( sk_D @ X23 @ X25 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','17','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('45',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v4_pre_topc @ X41 @ X42 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('51',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('54',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('55',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('56',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ( v4_pre_topc @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('57',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','52','53','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1dvHZITXU
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.22/0.35  % Running in FO mode
% 3.97/4.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.97/4.15  % Solved by: fo/fo7.sh
% 3.97/4.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.97/4.15  % done 6101 iterations in 3.683s
% 3.97/4.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.97/4.15  % SZS output start Refutation
% 3.97/4.15  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.97/4.15  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.97/4.15  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.97/4.15  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.97/4.15  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.97/4.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.97/4.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.97/4.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.97/4.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.97/4.15  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.97/4.15  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.97/4.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.97/4.15  thf(sk_A_type, type, sk_A: $i).
% 3.97/4.15  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.97/4.15  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.97/4.15  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.97/4.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.97/4.15  thf(t29_tops_1, conjecture,
% 3.97/4.15    (![A:$i]:
% 3.97/4.15     ( ( l1_pre_topc @ A ) =>
% 3.97/4.15       ( ![B:$i]:
% 3.97/4.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.97/4.15           ( ( v4_pre_topc @ B @ A ) <=>
% 3.97/4.15             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 3.97/4.15  thf(zf_stmt_0, negated_conjecture,
% 3.97/4.15    (~( ![A:$i]:
% 3.97/4.15        ( ( l1_pre_topc @ A ) =>
% 3.97/4.15          ( ![B:$i]:
% 3.97/4.15            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.97/4.15              ( ( v4_pre_topc @ B @ A ) <=>
% 3.97/4.15                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 3.97/4.15    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 3.97/4.15  thf('0', plain,
% 3.97/4.15      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 3.97/4.15        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('1', plain,
% 3.97/4.15      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)) | 
% 3.97/4.15       ~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('split', [status(esa)], ['0'])).
% 3.97/4.15  thf('2', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf(dt_k3_subset_1, axiom,
% 3.97/4.15    (![A:$i,B:$i]:
% 3.97/4.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.97/4.15       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.97/4.15  thf('3', plain,
% 3.97/4.15      (![X3 : $i, X4 : $i]:
% 3.97/4.15         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 3.97/4.15          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 3.97/4.15      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.97/4.15  thf('4', plain,
% 3.97/4.15      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['2', '3'])).
% 3.97/4.15  thf('5', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf(t25_pre_topc, axiom,
% 3.97/4.15    (![A:$i]:
% 3.97/4.15     ( ( l1_struct_0 @ A ) =>
% 3.97/4.15       ( ![B:$i]:
% 3.97/4.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.97/4.15           ( ![C:$i]:
% 3.97/4.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.97/4.15               ( ( ( ( k2_struct_0 @ A ) =
% 3.97/4.15                     ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) & 
% 3.97/4.15                   ( r1_xboole_0 @ B @ C ) ) =>
% 3.97/4.15                 ( ( C ) =
% 3.97/4.15                   ( k7_subset_1 @
% 3.97/4.15                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 3.97/4.15  thf('6', plain,
% 3.97/4.15      (![X54 : $i, X55 : $i, X56 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 3.97/4.15          | ((k2_struct_0 @ X55)
% 3.97/4.15              != (k4_subset_1 @ (u1_struct_0 @ X55) @ X54 @ X56))
% 3.97/4.15          | ~ (r1_xboole_0 @ X54 @ X56)
% 3.97/4.15          | ((X56)
% 3.97/4.15              = (k7_subset_1 @ (u1_struct_0 @ X55) @ (k2_struct_0 @ X55) @ X54))
% 3.97/4.15          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 3.97/4.15          | ~ (l1_struct_0 @ X55))),
% 3.97/4.15      inference('cnf', [status(esa)], [t25_pre_topc])).
% 3.97/4.15  thf('7', plain,
% 3.97/4.15      (![X0 : $i]:
% 3.97/4.15         (~ (l1_struct_0 @ sk_A)
% 3.97/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.97/4.15          | ((X0)
% 3.97/4.15              = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 3.97/4.15                 sk_B_1))
% 3.97/4.15          | ~ (r1_xboole_0 @ sk_B_1 @ X0)
% 3.97/4.15          | ((k2_struct_0 @ sk_A)
% 3.97/4.15              != (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.15  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf(dt_l1_pre_topc, axiom,
% 3.97/4.15    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.97/4.15  thf('9', plain, (![X46 : $i]: ((l1_struct_0 @ X46) | ~ (l1_pre_topc @ X46))),
% 3.97/4.15      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.97/4.15  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 3.97/4.15      inference('sup-', [status(thm)], ['8', '9'])).
% 3.97/4.15  thf('11', plain,
% 3.97/4.15      (![X0 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.97/4.15          | ((X0)
% 3.97/4.15              = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 3.97/4.15                 sk_B_1))
% 3.97/4.15          | ~ (r1_xboole_0 @ sk_B_1 @ X0)
% 3.97/4.15          | ((k2_struct_0 @ sk_A)
% 3.97/4.15              != (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)))),
% 3.97/4.15      inference('demod', [status(thm)], ['7', '10'])).
% 3.97/4.15  thf('12', plain,
% 3.97/4.15      ((((k2_struct_0 @ sk_A)
% 3.97/4.15          != (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.97/4.15              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 3.97/4.15        | ~ (r1_xboole_0 @ sk_B_1 @ 
% 3.97/4.15             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 3.97/4.15        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 3.97/4.15            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 3.97/4.15               sk_B_1)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['4', '11'])).
% 3.97/4.15  thf('13', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf(t18_pre_topc, axiom,
% 3.97/4.15    (![A:$i]:
% 3.97/4.15     ( ( l1_struct_0 @ A ) =>
% 3.97/4.15       ( ![B:$i]:
% 3.97/4.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.97/4.15           ( ( k4_subset_1 @
% 3.97/4.15               ( u1_struct_0 @ A ) @ B @ 
% 3.97/4.15               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 3.97/4.15             ( k2_struct_0 @ A ) ) ) ) ))).
% 3.97/4.15  thf('14', plain,
% 3.97/4.15      (![X48 : $i, X49 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 3.97/4.15          | ((k4_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 3.97/4.15              (k3_subset_1 @ (u1_struct_0 @ X49) @ X48)) = (k2_struct_0 @ X49))
% 3.97/4.15          | ~ (l1_struct_0 @ X49))),
% 3.97/4.15      inference('cnf', [status(esa)], [t18_pre_topc])).
% 3.97/4.15  thf('15', plain,
% 3.97/4.15      ((~ (l1_struct_0 @ sk_A)
% 3.97/4.15        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.97/4.15            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 3.97/4.15            = (k2_struct_0 @ sk_A)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['13', '14'])).
% 3.97/4.15  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 3.97/4.15      inference('sup-', [status(thm)], ['8', '9'])).
% 3.97/4.15  thf('17', plain,
% 3.97/4.15      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.97/4.15         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (k2_struct_0 @ sk_A))),
% 3.97/4.15      inference('demod', [status(thm)], ['15', '16'])).
% 3.97/4.15  thf('18', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('19', plain,
% 3.97/4.15      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['2', '3'])).
% 3.97/4.15  thf(t43_subset_1, axiom,
% 3.97/4.15    (![A:$i,B:$i]:
% 3.97/4.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.97/4.15       ( ![C:$i]:
% 3.97/4.15         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.97/4.15           ( ( r1_xboole_0 @ B @ C ) <=>
% 3.97/4.15             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 3.97/4.15  thf('20', plain,
% 3.97/4.15      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 3.97/4.15          | ~ (r1_tarski @ X21 @ (k3_subset_1 @ X20 @ X19))
% 3.97/4.15          | (r1_xboole_0 @ X21 @ X19)
% 3.97/4.15          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 3.97/4.15      inference('cnf', [status(esa)], [t43_subset_1])).
% 3.97/4.15  thf('21', plain,
% 3.97/4.15      (![X0 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.97/4.15          | (r1_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 3.97/4.15          | ~ (r1_tarski @ X0 @ 
% 3.97/4.15               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.97/4.15                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 3.97/4.15      inference('sup-', [status(thm)], ['19', '20'])).
% 3.97/4.15  thf('22', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf(involutiveness_k3_subset_1, axiom,
% 3.97/4.15    (![A:$i,B:$i]:
% 3.97/4.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.97/4.15       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.97/4.15  thf('23', plain,
% 3.97/4.15      (![X11 : $i, X12 : $i]:
% 3.97/4.15         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 3.97/4.15          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.97/4.15      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.97/4.15  thf('24', plain,
% 3.97/4.15      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.97/4.15         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 3.97/4.15      inference('sup-', [status(thm)], ['22', '23'])).
% 3.97/4.15  thf('25', plain,
% 3.97/4.15      (![X0 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.97/4.15          | (r1_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 3.97/4.15          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 3.97/4.15      inference('demod', [status(thm)], ['21', '24'])).
% 3.97/4.15  thf('26', plain,
% 3.97/4.15      ((~ (r1_tarski @ sk_B_1 @ sk_B_1)
% 3.97/4.15        | (r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['18', '25'])).
% 3.97/4.15  thf('27', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('28', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf(t7_subset_1, axiom,
% 3.97/4.15    (![A:$i,B:$i]:
% 3.97/4.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.97/4.15       ( ![C:$i]:
% 3.97/4.15         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.97/4.15           ( ( ![D:$i]:
% 3.97/4.15               ( ( m1_subset_1 @ D @ A ) =>
% 3.97/4.15                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 3.97/4.15             ( r1_tarski @ B @ C ) ) ) ) ))).
% 3.97/4.15  thf('29', plain,
% 3.97/4.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 3.97/4.15          | (r1_tarski @ X25 @ X23)
% 3.97/4.15          | (r2_hidden @ (sk_D @ X23 @ X25 @ X24) @ X25)
% 3.97/4.15          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 3.97/4.15      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.97/4.15  thf('30', plain,
% 3.97/4.15      (![X0 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.97/4.15          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 3.97/4.15          | (r1_tarski @ X0 @ sk_B_1))),
% 3.97/4.15      inference('sup-', [status(thm)], ['28', '29'])).
% 3.97/4.15  thf('31', plain,
% 3.97/4.15      (((r1_tarski @ sk_B_1 @ sk_B_1)
% 3.97/4.15        | (r2_hidden @ (sk_D @ sk_B_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1))),
% 3.97/4.15      inference('sup-', [status(thm)], ['27', '30'])).
% 3.97/4.15  thf('32', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('33', plain,
% 3.97/4.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 3.97/4.15          | (r1_tarski @ X25 @ X23)
% 3.97/4.15          | ~ (r2_hidden @ (sk_D @ X23 @ X25 @ X24) @ X23)
% 3.97/4.15          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 3.97/4.15      inference('cnf', [status(esa)], [t7_subset_1])).
% 3.97/4.15  thf('34', plain,
% 3.97/4.15      (![X0 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.97/4.15          | ~ (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 3.97/4.15          | (r1_tarski @ X0 @ sk_B_1))),
% 3.97/4.15      inference('sup-', [status(thm)], ['32', '33'])).
% 3.97/4.15  thf('35', plain,
% 3.97/4.15      (((r1_tarski @ sk_B_1 @ sk_B_1)
% 3.97/4.15        | (r1_tarski @ sk_B_1 @ sk_B_1)
% 3.97/4.15        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.97/4.15      inference('sup-', [status(thm)], ['31', '34'])).
% 3.97/4.15  thf('36', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('37', plain,
% 3.97/4.15      (((r1_tarski @ sk_B_1 @ sk_B_1) | (r1_tarski @ sk_B_1 @ sk_B_1))),
% 3.97/4.15      inference('demod', [status(thm)], ['35', '36'])).
% 3.97/4.15  thf('38', plain, ((r1_tarski @ sk_B_1 @ sk_B_1)),
% 3.97/4.15      inference('simplify', [status(thm)], ['37'])).
% 3.97/4.15  thf('39', plain,
% 3.97/4.15      ((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 3.97/4.15      inference('demod', [status(thm)], ['26', '38'])).
% 3.97/4.15  thf('40', plain,
% 3.97/4.15      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.97/4.15        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 3.97/4.15            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 3.97/4.15               sk_B_1)))),
% 3.97/4.15      inference('demod', [status(thm)], ['12', '17', '39'])).
% 3.97/4.15  thf('41', plain,
% 3.97/4.15      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 3.97/4.15         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 3.97/4.15      inference('simplify', [status(thm)], ['40'])).
% 3.97/4.15  thf('42', plain,
% 3.97/4.15      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 3.97/4.15        | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('43', plain,
% 3.97/4.15      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 3.97/4.15      inference('split', [status(esa)], ['42'])).
% 3.97/4.15  thf('44', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf(d6_pre_topc, axiom,
% 3.97/4.15    (![A:$i]:
% 3.97/4.15     ( ( l1_pre_topc @ A ) =>
% 3.97/4.15       ( ![B:$i]:
% 3.97/4.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.97/4.15           ( ( v4_pre_topc @ B @ A ) <=>
% 3.97/4.15             ( v3_pre_topc @
% 3.97/4.15               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 3.97/4.15               A ) ) ) ) ))).
% 3.97/4.15  thf('45', plain,
% 3.97/4.15      (![X41 : $i, X42 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 3.97/4.15          | ~ (v4_pre_topc @ X41 @ X42)
% 3.97/4.15          | (v3_pre_topc @ 
% 3.97/4.15             (k7_subset_1 @ (u1_struct_0 @ X42) @ (k2_struct_0 @ X42) @ X41) @ 
% 3.97/4.15             X42)
% 3.97/4.15          | ~ (l1_pre_topc @ X42))),
% 3.97/4.15      inference('cnf', [status(esa)], [d6_pre_topc])).
% 3.97/4.15  thf('46', plain,
% 3.97/4.15      ((~ (l1_pre_topc @ sk_A)
% 3.97/4.15        | (v3_pre_topc @ 
% 3.97/4.15           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15           sk_A)
% 3.97/4.15        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('sup-', [status(thm)], ['44', '45'])).
% 3.97/4.15  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('48', plain,
% 3.97/4.15      (((v3_pre_topc @ 
% 3.97/4.15         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15         sk_A)
% 3.97/4.15        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('demod', [status(thm)], ['46', '47'])).
% 3.97/4.15  thf('49', plain,
% 3.97/4.15      (((v3_pre_topc @ 
% 3.97/4.15         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15         sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['43', '48'])).
% 3.97/4.15  thf('50', plain,
% 3.97/4.15      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 3.97/4.15         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 3.97/4.15      inference('sup+', [status(thm)], ['41', '49'])).
% 3.97/4.15  thf('51', plain,
% 3.97/4.15      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 3.97/4.15         <= (~
% 3.97/4.15             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15               sk_A)))),
% 3.97/4.15      inference('split', [status(esa)], ['0'])).
% 3.97/4.15  thf('52', plain,
% 3.97/4.15      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)) | 
% 3.97/4.15       ~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('sup-', [status(thm)], ['50', '51'])).
% 3.97/4.15  thf('53', plain,
% 3.97/4.15      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)) | 
% 3.97/4.15       ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('split', [status(esa)], ['42'])).
% 3.97/4.15  thf('54', plain,
% 3.97/4.15      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 3.97/4.15         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15               sk_A)))),
% 3.97/4.15      inference('split', [status(esa)], ['42'])).
% 3.97/4.15  thf('55', plain,
% 3.97/4.15      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 3.97/4.15         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 3.97/4.15      inference('simplify', [status(thm)], ['40'])).
% 3.97/4.15  thf('56', plain,
% 3.97/4.15      (![X41 : $i, X42 : $i]:
% 3.97/4.15         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 3.97/4.15          | ~ (v3_pre_topc @ 
% 3.97/4.15               (k7_subset_1 @ (u1_struct_0 @ X42) @ (k2_struct_0 @ X42) @ X41) @ 
% 3.97/4.15               X42)
% 3.97/4.15          | (v4_pre_topc @ X41 @ X42)
% 3.97/4.15          | ~ (l1_pre_topc @ X42))),
% 3.97/4.15      inference('cnf', [status(esa)], [d6_pre_topc])).
% 3.97/4.15  thf('57', plain,
% 3.97/4.15      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 3.97/4.15        | ~ (l1_pre_topc @ sk_A)
% 3.97/4.15        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 3.97/4.15        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.97/4.15      inference('sup-', [status(thm)], ['55', '56'])).
% 3.97/4.15  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('59', plain,
% 3.97/4.15      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.97/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.15  thf('60', plain,
% 3.97/4.15      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 3.97/4.15        | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('demod', [status(thm)], ['57', '58', '59'])).
% 3.97/4.15  thf('61', plain,
% 3.97/4.15      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 3.97/4.15         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 3.97/4.15               sk_A)))),
% 3.97/4.15      inference('sup-', [status(thm)], ['54', '60'])).
% 3.97/4.15  thf('62', plain,
% 3.97/4.15      ((~ (v4_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 3.97/4.15      inference('split', [status(esa)], ['0'])).
% 3.97/4.15  thf('63', plain,
% 3.97/4.15      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)) | 
% 3.97/4.15       ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 3.97/4.15      inference('sup-', [status(thm)], ['61', '62'])).
% 3.97/4.15  thf('64', plain, ($false),
% 3.97/4.15      inference('sat_resolution*', [status(thm)], ['1', '52', '53', '63'])).
% 3.97/4.15  
% 3.97/4.15  % SZS output end Refutation
% 3.97/4.15  
% 3.97/4.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
