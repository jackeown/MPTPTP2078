%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zyX6EY7EYc

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:52 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 434 expanded)
%              Number of leaves         :   39 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          : 1320 (4740 expanded)
%              Number of equality atoms :   99 ( 306 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_pre_topc @ X37 @ X36 ) @ ( k1_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('18',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( ( k2_pre_topc @ X31 @ X30 )
        = X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_pre_topc @ X39 @ X38 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ ( k2_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('56',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','75'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('92',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','89','90','91'])).

thf('93',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('95',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X34 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('96',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','99'])).

thf('101',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('102',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('104',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','102','103'])).

thf('105',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['25','104'])).

thf('106',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','105','106','107','108'])).

thf('110',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('112',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['27','102'])).

thf('114',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['109','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zyX6EY7EYc
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 1740 iterations in 0.660s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.12  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.91/1.12  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.91/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.91/1.12  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.91/1.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.91/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.12  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.91/1.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.91/1.12  thf(t77_tops_1, conjecture,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( v4_pre_topc @ B @ A ) <=>
% 0.91/1.12             ( ( k2_tops_1 @ A @ B ) =
% 0.91/1.12               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i]:
% 0.91/1.12        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.12          ( ![B:$i]:
% 0.91/1.12            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12              ( ( v4_pre_topc @ B @ A ) <=>
% 0.91/1.12                ( ( k2_tops_1 @ A @ B ) =
% 0.91/1.12                  ( k7_subset_1 @
% 0.91/1.12                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.91/1.12  thf('0', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(d5_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.91/1.12  thf('1', plain,
% 0.91/1.12      (![X17 : $i, X18 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.91/1.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('2', plain,
% 0.91/1.12      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.91/1.12         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.91/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.12  thf(t36_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.12  thf('3', plain,
% 0.91/1.12      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.91/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.91/1.12  thf(t3_subset, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.12  thf('4', plain,
% 0.91/1.12      (![X27 : $i, X29 : $i]:
% 0.91/1.12         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('5', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.12  thf('6', plain,
% 0.91/1.12      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.91/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['2', '5'])).
% 0.91/1.12  thf('7', plain,
% 0.91/1.12      (![X17 : $i, X18 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.91/1.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('8', plain,
% 0.91/1.12      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.91/1.12         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf('9', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(involutiveness_k3_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.91/1.12  thf('10', plain,
% 0.91/1.12      (![X19 : $i, X20 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.91/1.12          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.91/1.12      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.91/1.12  thf('11', plain,
% 0.91/1.12      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.91/1.12      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.12  thf('12', plain,
% 0.91/1.12      (((sk_B)
% 0.91/1.12         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['8', '11'])).
% 0.91/1.12  thf('13', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.12  thf(l78_tops_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( l1_pre_topc @ A ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( k2_tops_1 @ A @ B ) =
% 0.91/1.12             ( k7_subset_1 @
% 0.91/1.12               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.91/1.12               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.91/1.12  thf('14', plain,
% 0.91/1.12      (![X36 : $i, X37 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.91/1.12          | ((k2_tops_1 @ X37 @ X36)
% 0.91/1.12              = (k7_subset_1 @ (u1_struct_0 @ X37) @ 
% 0.91/1.12                 (k2_pre_topc @ X37 @ X36) @ (k1_tops_1 @ X37 @ X36)))
% 0.91/1.12          | ~ (l1_pre_topc @ X37))),
% 0.91/1.12      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.91/1.12  thf('15', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (~ (l1_pre_topc @ X0)
% 0.91/1.12          | ((k2_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.91/1.12              = (k7_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.91/1.12                 (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.91/1.12                 (k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['13', '14'])).
% 0.91/1.12  thf('16', plain,
% 0.91/1.12      ((((k2_tops_1 @ sk_A @ 
% 0.91/1.12          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.91/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12             (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.12             (k1_tops_1 @ sk_A @ 
% 0.91/1.12              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 0.91/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.12      inference('sup+', [status(thm)], ['12', '15'])).
% 0.91/1.12  thf('17', plain,
% 0.91/1.12      (((sk_B)
% 0.91/1.12         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['8', '11'])).
% 0.91/1.12  thf('18', plain,
% 0.91/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12             (k1_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('19', plain,
% 0.91/1.12      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.91/1.12      inference('split', [status(esa)], ['18'])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(t52_pre_topc, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( l1_pre_topc @ A ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.91/1.12             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.91/1.12               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.91/1.12  thf('21', plain,
% 0.91/1.12      (![X30 : $i, X31 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.91/1.12          | ~ (v4_pre_topc @ X30 @ X31)
% 0.91/1.12          | ((k2_pre_topc @ X31 @ X30) = (X30))
% 0.91/1.12          | ~ (l1_pre_topc @ X31))),
% 0.91/1.12      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.91/1.12  thf('22', plain,
% 0.91/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.12        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.91/1.12        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.12  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('24', plain,
% 0.91/1.12      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['22', '23'])).
% 0.91/1.12  thf('25', plain,
% 0.91/1.12      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.91/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['19', '24'])).
% 0.91/1.12  thf('26', plain,
% 0.91/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12              (k1_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('27', plain,
% 0.91/1.12      (~
% 0.91/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.91/1.12       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.91/1.12      inference('split', [status(esa)], ['26'])).
% 0.91/1.12  thf('28', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(dt_k2_tops_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.12       ( m1_subset_1 @
% 0.91/1.12         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      (![X32 : $i, X33 : $i]:
% 0.91/1.12         (~ (l1_pre_topc @ X32)
% 0.91/1.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.91/1.12          | (m1_subset_1 @ (k2_tops_1 @ X32 @ X33) @ 
% 0.91/1.12             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.91/1.12  thf('30', plain,
% 0.91/1.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.12  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('32', plain,
% 0.91/1.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('33', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(redefinition_k4_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.91/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.12       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.91/1.12  thf('34', plain,
% 0.91/1.12      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.91/1.12          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.91/1.12          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.91/1.12  thf('35', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.91/1.12            = (k2_xboole_0 @ sk_B @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.12  thf('36', plain,
% 0.91/1.12      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.91/1.12         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['32', '35'])).
% 0.91/1.12  thf('37', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(t65_tops_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( l1_pre_topc @ A ) =>
% 0.91/1.12       ( ![B:$i]:
% 0.91/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.12           ( ( k2_pre_topc @ A @ B ) =
% 0.91/1.12             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.91/1.12  thf('38', plain,
% 0.91/1.12      (![X38 : $i, X39 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.91/1.12          | ((k2_pre_topc @ X39 @ X38)
% 0.91/1.12              = (k4_subset_1 @ (u1_struct_0 @ X39) @ X38 @ 
% 0.91/1.12                 (k2_tops_1 @ X39 @ X38)))
% 0.91/1.12          | ~ (l1_pre_topc @ X39))),
% 0.91/1.12      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.91/1.12  thf('39', plain,
% 0.91/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.12        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.91/1.12            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.12  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('41', plain,
% 0.91/1.12      (((k2_pre_topc @ sk_A @ sk_B)
% 0.91/1.12         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['39', '40'])).
% 0.91/1.12  thf('42', plain,
% 0.91/1.12      (((k2_pre_topc @ sk_A @ sk_B)
% 0.91/1.12         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['36', '41'])).
% 0.91/1.12  thf('43', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(redefinition_k7_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.91/1.12  thf('44', plain,
% 0.91/1.12      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.91/1.12          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.91/1.12  thf('45', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.91/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.12  thf('46', plain,
% 0.91/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12             (k1_tops_1 @ sk_A @ sk_B))))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('split', [status(esa)], ['18'])).
% 0.91/1.12  thf('47', plain,
% 0.91/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['45', '46'])).
% 0.91/1.12  thf('48', plain,
% 0.91/1.12      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.91/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.91/1.12  thf('49', plain,
% 0.91/1.12      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['47', '48'])).
% 0.91/1.12  thf(t28_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.12  thf('50', plain,
% 0.91/1.12      (![X8 : $i, X9 : $i]:
% 0.91/1.12         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.91/1.12      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.12  thf('51', plain,
% 0.91/1.12      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.91/1.12          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.12  thf(t100_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.12  thf('52', plain,
% 0.91/1.12      (![X5 : $i, X6 : $i]:
% 0.91/1.12         ((k4_xboole_0 @ X5 @ X6)
% 0.91/1.12           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.12  thf(t39_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.12  thf('53', plain,
% 0.91/1.12      (![X12 : $i, X13 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.91/1.12           = (k2_xboole_0 @ X12 @ X13))),
% 0.91/1.12      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.12  thf('54', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.91/1.12           = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.12      inference('sup+', [status(thm)], ['52', '53'])).
% 0.91/1.12  thf('55', plain,
% 0.91/1.12      ((((k2_xboole_0 @ sk_B @ 
% 0.91/1.12          (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.91/1.12          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['51', '54'])).
% 0.91/1.12  thf(t1_boole, axiom,
% 0.91/1.12    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.12  thf('56', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.91/1.12      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.12  thf('57', plain,
% 0.91/1.12      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.91/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.91/1.12  thf(t44_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.91/1.12       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.91/1.12  thf('58', plain,
% 0.91/1.12      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.12         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.91/1.12          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 0.91/1.12      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.91/1.12  thf('59', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['57', '58'])).
% 0.91/1.12  thf('60', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.12      inference('sup+', [status(thm)], ['56', '59'])).
% 0.91/1.12  thf('61', plain,
% 0.91/1.12      (![X27 : $i, X29 : $i]:
% 0.91/1.12         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('62', plain,
% 0.91/1.12      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['60', '61'])).
% 0.91/1.12  thf('63', plain,
% 0.91/1.12      (![X19 : $i, X20 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.91/1.12          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.91/1.12      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.91/1.12  thf('64', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['62', '63'])).
% 0.91/1.12  thf('65', plain,
% 0.91/1.12      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['60', '61'])).
% 0.91/1.12  thf('66', plain,
% 0.91/1.12      (![X17 : $i, X18 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.91/1.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('67', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['65', '66'])).
% 0.91/1.12  thf('68', plain,
% 0.91/1.12      (![X12 : $i, X13 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.91/1.12           = (k2_xboole_0 @ X12 @ X13))),
% 0.91/1.12      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.12  thf(commutativity_k2_xboole_0, axiom,
% 0.91/1.12    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.91/1.12  thf('69', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.12      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.12  thf('70', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.91/1.12      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.12  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['69', '70'])).
% 0.91/1.12  thf('72', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['68', '71'])).
% 0.91/1.12  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['69', '70'])).
% 0.91/1.12  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['72', '73'])).
% 0.91/1.12  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['67', '74'])).
% 0.91/1.12  thf('76', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.12      inference('demod', [status(thm)], ['64', '75'])).
% 0.91/1.12  thf(d10_xboole_0, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.12  thf('77', plain,
% 0.91/1.12      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.12  thf('78', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.91/1.12      inference('simplify', [status(thm)], ['77'])).
% 0.91/1.12  thf('79', plain,
% 0.91/1.12      (![X27 : $i, X29 : $i]:
% 0.91/1.12         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('80', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.12  thf('81', plain,
% 0.91/1.12      (![X17 : $i, X18 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.91/1.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('82', plain,
% 0.91/1.12      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['80', '81'])).
% 0.91/1.12  thf('83', plain,
% 0.91/1.12      (![X5 : $i, X6 : $i]:
% 0.91/1.12         ((k4_xboole_0 @ X5 @ X6)
% 0.91/1.12           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.12  thf('84', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k3_subset_1 @ X0 @ X0)
% 0.91/1.12           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['82', '83'])).
% 0.91/1.12  thf('85', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.91/1.12      inference('simplify', [status(thm)], ['77'])).
% 0.91/1.12  thf('86', plain,
% 0.91/1.12      (![X8 : $i, X9 : $i]:
% 0.91/1.12         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.91/1.12      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.12  thf('87', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['85', '86'])).
% 0.91/1.12  thf('88', plain,
% 0.91/1.12      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.12      inference('demod', [status(thm)], ['84', '87'])).
% 0.91/1.12  thf('89', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.12      inference('demod', [status(thm)], ['76', '88'])).
% 0.91/1.12  thf('90', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.12      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.12  thf('91', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['69', '70'])).
% 0.91/1.12  thf('92', plain,
% 0.91/1.12      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('demod', [status(thm)], ['55', '89', '90', '91'])).
% 0.91/1.12  thf('93', plain,
% 0.91/1.12      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['42', '92'])).
% 0.91/1.12  thf('94', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(fc1_tops_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.91/1.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.12       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.91/1.12  thf('95', plain,
% 0.91/1.12      (![X34 : $i, X35 : $i]:
% 0.91/1.12         (~ (l1_pre_topc @ X34)
% 0.91/1.12          | ~ (v2_pre_topc @ X34)
% 0.91/1.12          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.91/1.12          | (v4_pre_topc @ (k2_pre_topc @ X34 @ X35) @ X34))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.91/1.12  thf('96', plain,
% 0.91/1.12      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.91/1.12        | ~ (v2_pre_topc @ sk_A)
% 0.91/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['94', '95'])).
% 0.91/1.12  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('99', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.91/1.12      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.91/1.12  thf('100', plain,
% 0.91/1.12      (((v4_pre_topc @ sk_B @ sk_A))
% 0.91/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['93', '99'])).
% 0.91/1.12  thf('101', plain,
% 0.91/1.12      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.91/1.12      inference('split', [status(esa)], ['26'])).
% 0.91/1.12  thf('102', plain,
% 0.91/1.12      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.91/1.12       ~
% 0.91/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['100', '101'])).
% 0.91/1.12  thf('103', plain,
% 0.91/1.12      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.91/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.91/1.12      inference('split', [status(esa)], ['18'])).
% 0.91/1.12  thf('104', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.91/1.12      inference('sat_resolution*', [status(thm)], ['27', '102', '103'])).
% 0.91/1.12  thf('105', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.91/1.12      inference('simpl_trail', [status(thm)], ['25', '104'])).
% 0.91/1.12  thf('106', plain,
% 0.91/1.12      (((sk_B)
% 0.91/1.12         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.12            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['8', '11'])).
% 0.91/1.12  thf('107', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.91/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.12  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('109', plain,
% 0.91/1.12      (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)],
% 0.91/1.12                ['16', '17', '105', '106', '107', '108'])).
% 0.91/1.12  thf('110', plain,
% 0.91/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12              (k1_tops_1 @ sk_A @ sk_B))))
% 0.91/1.12         <= (~
% 0.91/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('split', [status(esa)], ['26'])).
% 0.91/1.12  thf('111', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.91/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.12  thf('112', plain,
% 0.91/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.91/1.12         <= (~
% 0.91/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.12      inference('demod', [status(thm)], ['110', '111'])).
% 0.91/1.12  thf('113', plain,
% 0.91/1.12      (~
% 0.91/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.91/1.12             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.91/1.12      inference('sat_resolution*', [status(thm)], ['27', '102'])).
% 0.91/1.12  thf('114', plain,
% 0.91/1.12      (((k2_tops_1 @ sk_A @ sk_B)
% 0.91/1.12         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 0.91/1.12  thf('115', plain, ($false),
% 0.91/1.12      inference('simplify_reflect-', [status(thm)], ['109', '114'])).
% 0.91/1.12  
% 0.91/1.12  % SZS output end Refutation
% 0.91/1.12  
% 0.91/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
