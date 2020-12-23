%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F3C22UvFud

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:54 EST 2020

% Result     : Theorem 2.56s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 332 expanded)
%              Number of leaves         :   35 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          : 1383 (4715 expanded)
%              Number of equality atoms :   83 ( 245 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X19 @ X17 )
        = ( k9_subset_1 @ X18 @ X19 @ ( k3_subset_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( k4_xboole_0 @ sk_B @ X0 ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_tops_1 @ X26 @ X25 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ X25 ) @ ( k2_pre_topc @ X26 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X29 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('63',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','66'])).

thf('68',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('69',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('71',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['36','69','70'])).

thf('72',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['34','71'])).

thf('73',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('76',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k3_subset_1 @ X21 @ ( k7_subset_1 @ X21 @ X22 @ X20 ) )
        = ( k4_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X22 ) @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('80',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('83',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('88',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_tops_1 @ X32 @ X31 )
        = ( k2_tops_1 @ X32 @ ( k3_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','91'])).

thf('93',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80','92'])).

thf('94',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','93'])).

thf('95',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','94'])).

thf('96',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['35'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['36','69'])).

thf('100',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F3C22UvFud
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.56/2.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.56/2.76  % Solved by: fo/fo7.sh
% 2.56/2.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.56/2.76  % done 1593 iterations in 2.305s
% 2.56/2.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.56/2.76  % SZS output start Refutation
% 2.56/2.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.56/2.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.56/2.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.56/2.76  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.56/2.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.56/2.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.56/2.76  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.56/2.76  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.56/2.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.56/2.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.56/2.76  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.56/2.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.56/2.76  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.56/2.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.56/2.76  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.56/2.76  thf(sk_B_type, type, sk_B: $i).
% 2.56/2.76  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.56/2.76  thf(sk_A_type, type, sk_A: $i).
% 2.56/2.76  thf(t77_tops_1, conjecture,
% 2.56/2.76    (![A:$i]:
% 2.56/2.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.56/2.76       ( ![B:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.56/2.76           ( ( v4_pre_topc @ B @ A ) <=>
% 2.56/2.76             ( ( k2_tops_1 @ A @ B ) =
% 2.56/2.76               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 2.56/2.76  thf(zf_stmt_0, negated_conjecture,
% 2.56/2.76    (~( ![A:$i]:
% 2.56/2.76        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.56/2.76          ( ![B:$i]:
% 2.56/2.76            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.56/2.76              ( ( v4_pre_topc @ B @ A ) <=>
% 2.56/2.76                ( ( k2_tops_1 @ A @ B ) =
% 2.56/2.76                  ( k7_subset_1 @
% 2.56/2.76                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 2.56/2.76    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 2.56/2.76  thf('0', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(t74_tops_1, axiom,
% 2.56/2.76    (![A:$i]:
% 2.56/2.76     ( ( l1_pre_topc @ A ) =>
% 2.56/2.76       ( ![B:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.56/2.76           ( ( k1_tops_1 @ A @ B ) =
% 2.56/2.76             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.56/2.76  thf('1', plain,
% 2.56/2.76      (![X35 : $i, X36 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 2.56/2.76          | ((k1_tops_1 @ X36 @ X35)
% 2.56/2.76              = (k7_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 2.56/2.76                 (k2_tops_1 @ X36 @ X35)))
% 2.56/2.76          | ~ (l1_pre_topc @ X36))),
% 2.56/2.76      inference('cnf', [status(esa)], [t74_tops_1])).
% 2.56/2.76  thf('2', plain,
% 2.56/2.76      ((~ (l1_pre_topc @ sk_A)
% 2.56/2.76        | ((k1_tops_1 @ sk_A @ sk_B)
% 2.56/2.76            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76               (k2_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['0', '1'])).
% 2.56/2.76  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('4', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(redefinition_k7_subset_1, axiom,
% 2.56/2.76    (![A:$i,B:$i,C:$i]:
% 2.56/2.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.56/2.76       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.56/2.76  thf('5', plain,
% 2.56/2.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 2.56/2.76          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 2.56/2.76      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.56/2.76  thf('6', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.56/2.76           = (k4_xboole_0 @ sk_B @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.56/2.76  thf('7', plain,
% 2.56/2.76      (((k1_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('demod', [status(thm)], ['2', '3', '6'])).
% 2.56/2.76  thf('8', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('9', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(dt_k7_subset_1, axiom,
% 2.56/2.76    (![A:$i,B:$i,C:$i]:
% 2.56/2.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.56/2.76       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.56/2.76  thf('10', plain,
% 2.56/2.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 2.56/2.76          | (m1_subset_1 @ (k7_subset_1 @ X9 @ X8 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 2.56/2.76      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 2.56/2.76  thf('11', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 2.56/2.76          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['9', '10'])).
% 2.56/2.76  thf('12', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.56/2.76           = (k4_xboole_0 @ sk_B @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.56/2.76  thf('13', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.56/2.76          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('demod', [status(thm)], ['11', '12'])).
% 2.56/2.76  thf(t32_subset_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.56/2.76       ( ![C:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.56/2.76           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.56/2.76             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.56/2.76  thf('14', plain,
% 2.56/2.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 2.56/2.76          | ((k7_subset_1 @ X18 @ X19 @ X17)
% 2.56/2.76              = (k9_subset_1 @ X18 @ X19 @ (k3_subset_1 @ X18 @ X17)))
% 2.56/2.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 2.56/2.76      inference('cnf', [status(esa)], [t32_subset_1])).
% 2.56/2.76  thf('15', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.56/2.76          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 2.56/2.76              (k4_xboole_0 @ sk_B @ X0))
% 2.56/2.76              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ 
% 2.56/2.76                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76                  (k4_xboole_0 @ sk_B @ X0)))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['13', '14'])).
% 2.56/2.76  thf('16', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76           (k4_xboole_0 @ sk_B @ X0))
% 2.56/2.76           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['8', '15'])).
% 2.56/2.76  thf('17', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.56/2.76           = (k4_xboole_0 @ sk_B @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.56/2.76  thf('18', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))
% 2.56/2.76           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.56/2.76      inference('demod', [status(thm)], ['16', '17'])).
% 2.56/2.76  thf('19', plain,
% 2.56/2.76      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.56/2.76         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('sup+', [status(thm)], ['7', '18'])).
% 2.56/2.76  thf('20', plain,
% 2.56/2.76      (((k1_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('demod', [status(thm)], ['2', '3', '6'])).
% 2.56/2.76  thf('21', plain,
% 2.56/2.76      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.56/2.76         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('demod', [status(thm)], ['19', '20'])).
% 2.56/2.76  thf('22', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(d2_tops_1, axiom,
% 2.56/2.76    (![A:$i]:
% 2.56/2.76     ( ( l1_pre_topc @ A ) =>
% 2.56/2.76       ( ![B:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.56/2.76           ( ( k2_tops_1 @ A @ B ) =
% 2.56/2.76             ( k9_subset_1 @
% 2.56/2.76               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.56/2.76               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 2.56/2.76  thf('23', plain,
% 2.56/2.76      (![X25 : $i, X26 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 2.56/2.76          | ((k2_tops_1 @ X26 @ X25)
% 2.56/2.76              = (k9_subset_1 @ (u1_struct_0 @ X26) @ 
% 2.56/2.76                 (k2_pre_topc @ X26 @ X25) @ 
% 2.56/2.76                 (k2_pre_topc @ X26 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25))))
% 2.56/2.76          | ~ (l1_pre_topc @ X26))),
% 2.56/2.76      inference('cnf', [status(esa)], [d2_tops_1])).
% 2.56/2.76  thf('24', plain,
% 2.56/2.76      ((~ (l1_pre_topc @ sk_A)
% 2.56/2.76        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76               (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.56/2.76               (k2_pre_topc @ sk_A @ 
% 2.56/2.76                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['22', '23'])).
% 2.56/2.76  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('26', plain,
% 2.56/2.76      (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.56/2.76            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.56/2.76      inference('demod', [status(thm)], ['24', '25'])).
% 2.56/2.76  thf('27', plain,
% 2.56/2.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76             (k1_tops_1 @ sk_A @ sk_B)))
% 2.56/2.76        | (v4_pre_topc @ sk_B @ sk_A))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('28', plain,
% 2.56/2.76      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.56/2.76      inference('split', [status(esa)], ['27'])).
% 2.56/2.76  thf('29', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(t52_pre_topc, axiom,
% 2.56/2.76    (![A:$i]:
% 2.56/2.76     ( ( l1_pre_topc @ A ) =>
% 2.56/2.76       ( ![B:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.56/2.76           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 2.56/2.76             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 2.56/2.76               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.56/2.76  thf('30', plain,
% 2.56/2.76      (![X23 : $i, X24 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.56/2.76          | ~ (v4_pre_topc @ X23 @ X24)
% 2.56/2.76          | ((k2_pre_topc @ X24 @ X23) = (X23))
% 2.56/2.76          | ~ (l1_pre_topc @ X24))),
% 2.56/2.76      inference('cnf', [status(esa)], [t52_pre_topc])).
% 2.56/2.76  thf('31', plain,
% 2.56/2.76      ((~ (l1_pre_topc @ sk_A)
% 2.56/2.76        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 2.56/2.76        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.56/2.76      inference('sup-', [status(thm)], ['29', '30'])).
% 2.56/2.76  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('33', plain,
% 2.56/2.76      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.56/2.76      inference('demod', [status(thm)], ['31', '32'])).
% 2.56/2.76  thf('34', plain,
% 2.56/2.76      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.56/2.76         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['28', '33'])).
% 2.56/2.76  thf('35', plain,
% 2.56/2.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76              (k1_tops_1 @ sk_A @ sk_B)))
% 2.56/2.76        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('36', plain,
% 2.56/2.76      (~
% 2.56/2.76       (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 2.56/2.76       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 2.56/2.76      inference('split', [status(esa)], ['35'])).
% 2.56/2.76  thf('37', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(t65_tops_1, axiom,
% 2.56/2.76    (![A:$i]:
% 2.56/2.76     ( ( l1_pre_topc @ A ) =>
% 2.56/2.76       ( ![B:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.56/2.76           ( ( k2_pre_topc @ A @ B ) =
% 2.56/2.76             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.56/2.76  thf('38', plain,
% 2.56/2.76      (![X33 : $i, X34 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.56/2.76          | ((k2_pre_topc @ X34 @ X33)
% 2.56/2.76              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 2.56/2.76                 (k2_tops_1 @ X34 @ X33)))
% 2.56/2.76          | ~ (l1_pre_topc @ X34))),
% 2.56/2.76      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.56/2.76  thf('39', plain,
% 2.56/2.76      ((~ (l1_pre_topc @ sk_A)
% 2.56/2.76        | ((k2_pre_topc @ sk_A @ sk_B)
% 2.56/2.76            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76               (k2_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['37', '38'])).
% 2.56/2.76  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('41', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(dt_k2_tops_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( ( l1_pre_topc @ A ) & 
% 2.56/2.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.56/2.76       ( m1_subset_1 @
% 2.56/2.76         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.56/2.76  thf('42', plain,
% 2.56/2.76      (![X27 : $i, X28 : $i]:
% 2.56/2.76         (~ (l1_pre_topc @ X27)
% 2.56/2.76          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.56/2.76          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 2.56/2.76             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 2.56/2.76      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.56/2.76  thf('43', plain,
% 2.56/2.76      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.56/2.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.56/2.76        | ~ (l1_pre_topc @ sk_A))),
% 2.56/2.76      inference('sup-', [status(thm)], ['41', '42'])).
% 2.56/2.76  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('45', plain,
% 2.56/2.76      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.56/2.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('demod', [status(thm)], ['43', '44'])).
% 2.56/2.76  thf('46', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(redefinition_k4_subset_1, axiom,
% 2.56/2.76    (![A:$i,B:$i,C:$i]:
% 2.56/2.76     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.56/2.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.56/2.76       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.56/2.76  thf('47', plain,
% 2.56/2.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 2.56/2.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 2.56/2.76          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 2.56/2.76      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.56/2.76  thf('48', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.56/2.76            = (k2_xboole_0 @ sk_B @ X0))
% 2.56/2.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['46', '47'])).
% 2.56/2.76  thf('49', plain,
% 2.56/2.76      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 2.56/2.76         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['45', '48'])).
% 2.56/2.76  thf('50', plain,
% 2.56/2.76      (((k2_pre_topc @ sk_A @ sk_B)
% 2.56/2.76         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('demod', [status(thm)], ['39', '40', '49'])).
% 2.56/2.76  thf('51', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.56/2.76           = (k4_xboole_0 @ sk_B @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.56/2.76  thf('52', plain,
% 2.56/2.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76             (k1_tops_1 @ sk_A @ sk_B))))
% 2.56/2.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.56/2.76      inference('split', [status(esa)], ['27'])).
% 2.56/2.76  thf('53', plain,
% 2.56/2.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.56/2.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.56/2.76      inference('sup+', [status(thm)], ['51', '52'])).
% 2.56/2.76  thf(t36_xboole_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.56/2.76  thf('54', plain,
% 2.56/2.76      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 2.56/2.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.56/2.76  thf(t12_xboole_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.56/2.76  thf('55', plain,
% 2.56/2.76      (![X2 : $i, X3 : $i]:
% 2.56/2.76         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.56/2.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.56/2.76  thf('56', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['54', '55'])).
% 2.56/2.76  thf(commutativity_k2_xboole_0, axiom,
% 2.56/2.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.56/2.76  thf('57', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.56/2.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.56/2.76  thf('58', plain,
% 2.56/2.76      (![X0 : $i, X1 : $i]:
% 2.56/2.76         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.56/2.76      inference('demod', [status(thm)], ['56', '57'])).
% 2.56/2.76  thf('59', plain,
% 2.56/2.76      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 2.56/2.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.56/2.76      inference('sup+', [status(thm)], ['53', '58'])).
% 2.56/2.76  thf('60', plain,
% 2.56/2.76      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 2.56/2.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.56/2.76      inference('sup+', [status(thm)], ['50', '59'])).
% 2.56/2.76  thf('61', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(fc1_tops_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.56/2.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.56/2.76       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 2.56/2.76  thf('62', plain,
% 2.56/2.76      (![X29 : $i, X30 : $i]:
% 2.56/2.76         (~ (l1_pre_topc @ X29)
% 2.56/2.76          | ~ (v2_pre_topc @ X29)
% 2.56/2.76          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.56/2.76          | (v4_pre_topc @ (k2_pre_topc @ X29 @ X30) @ X29))),
% 2.56/2.76      inference('cnf', [status(esa)], [fc1_tops_1])).
% 2.56/2.76  thf('63', plain,
% 2.56/2.76      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.56/2.76        | ~ (v2_pre_topc @ sk_A)
% 2.56/2.76        | ~ (l1_pre_topc @ sk_A))),
% 2.56/2.76      inference('sup-', [status(thm)], ['61', '62'])).
% 2.56/2.76  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('66', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.56/2.76      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.56/2.76  thf('67', plain,
% 2.56/2.76      (((v4_pre_topc @ sk_B @ sk_A))
% 2.56/2.76         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.56/2.76      inference('sup+', [status(thm)], ['60', '66'])).
% 2.56/2.76  thf('68', plain,
% 2.56/2.76      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 2.56/2.76      inference('split', [status(esa)], ['35'])).
% 2.56/2.76  thf('69', plain,
% 2.56/2.76      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 2.56/2.76       ~
% 2.56/2.76       (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76             (k1_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['67', '68'])).
% 2.56/2.76  thf('70', plain,
% 2.56/2.76      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 2.56/2.76       (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76             (k1_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('split', [status(esa)], ['27'])).
% 2.56/2.76  thf('71', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 2.56/2.76      inference('sat_resolution*', [status(thm)], ['36', '69', '70'])).
% 2.56/2.76  thf('72', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 2.56/2.76      inference('simpl_trail', [status(thm)], ['34', '71'])).
% 2.56/2.76  thf('73', plain,
% 2.56/2.76      (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.56/2.76      inference('demod', [status(thm)], ['26', '72'])).
% 2.56/2.76  thf('74', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('75', plain,
% 2.56/2.76      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 2.56/2.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('demod', [status(thm)], ['43', '44'])).
% 2.56/2.76  thf(t33_subset_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.56/2.76       ( ![C:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.56/2.76           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.56/2.76             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.56/2.76  thf('76', plain,
% 2.56/2.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 2.56/2.76          | ((k3_subset_1 @ X21 @ (k7_subset_1 @ X21 @ X22 @ X20))
% 2.56/2.76              = (k4_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X22) @ X20))
% 2.56/2.76          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 2.56/2.76      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.56/2.76  thf('77', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.56/2.76          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.56/2.76               (k2_tops_1 @ sk_A @ sk_B)))
% 2.56/2.76              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.56/2.76                 (k2_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['75', '76'])).
% 2.56/2.76  thf('78', plain,
% 2.56/2.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 2.56/2.76         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.56/2.76            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['74', '77'])).
% 2.56/2.76  thf('79', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.56/2.76           = (k4_xboole_0 @ sk_B @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.56/2.76  thf('80', plain,
% 2.56/2.76      (((k1_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('demod', [status(thm)], ['2', '3', '6'])).
% 2.56/2.76  thf('81', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(dt_k3_subset_1, axiom,
% 2.56/2.76    (![A:$i,B:$i]:
% 2.56/2.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.56/2.76       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.56/2.76  thf('82', plain,
% 2.56/2.76      (![X6 : $i, X7 : $i]:
% 2.56/2.76         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 2.56/2.76          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 2.56/2.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.56/2.76  thf('83', plain,
% 2.56/2.76      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.56/2.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('sup-', [status(thm)], ['81', '82'])).
% 2.56/2.76  thf('84', plain,
% 2.56/2.76      (![X33 : $i, X34 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.56/2.76          | ((k2_pre_topc @ X34 @ X33)
% 2.56/2.76              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 2.56/2.76                 (k2_tops_1 @ X34 @ X33)))
% 2.56/2.76          | ~ (l1_pre_topc @ X34))),
% 2.56/2.76      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.56/2.76  thf('85', plain,
% 2.56/2.76      ((~ (l1_pre_topc @ sk_A)
% 2.56/2.76        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.56/2.76            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.56/2.76               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['83', '84'])).
% 2.56/2.76  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('87', plain,
% 2.56/2.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf(t62_tops_1, axiom,
% 2.56/2.76    (![A:$i]:
% 2.56/2.76     ( ( l1_pre_topc @ A ) =>
% 2.56/2.76       ( ![B:$i]:
% 2.56/2.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.56/2.76           ( ( k2_tops_1 @ A @ B ) =
% 2.56/2.76             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 2.56/2.76  thf('88', plain,
% 2.56/2.76      (![X31 : $i, X32 : $i]:
% 2.56/2.76         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 2.56/2.76          | ((k2_tops_1 @ X32 @ X31)
% 2.56/2.76              = (k2_tops_1 @ X32 @ (k3_subset_1 @ (u1_struct_0 @ X32) @ X31)))
% 2.56/2.76          | ~ (l1_pre_topc @ X32))),
% 2.56/2.76      inference('cnf', [status(esa)], [t62_tops_1])).
% 2.56/2.76  thf('89', plain,
% 2.56/2.76      ((~ (l1_pre_topc @ sk_A)
% 2.56/2.76        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.56/2.76      inference('sup-', [status(thm)], ['87', '88'])).
% 2.56/2.76  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 2.56/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.56/2.76  thf('91', plain,
% 2.56/2.76      (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.56/2.76      inference('demod', [status(thm)], ['89', '90'])).
% 2.56/2.76  thf('92', plain,
% 2.56/2.76      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.56/2.76         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.56/2.76            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.56/2.76            (k2_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('demod', [status(thm)], ['85', '86', '91'])).
% 2.56/2.76  thf('93', plain,
% 2.56/2.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 2.56/2.76         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.56/2.76      inference('demod', [status(thm)], ['78', '79', '80', '92'])).
% 2.56/2.76  thf('94', plain,
% 2.56/2.76      (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('demod', [status(thm)], ['73', '93'])).
% 2.56/2.76  thf('95', plain,
% 2.56/2.76      (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('sup+', [status(thm)], ['21', '94'])).
% 2.56/2.76  thf('96', plain,
% 2.56/2.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76              (k1_tops_1 @ sk_A @ sk_B))))
% 2.56/2.76         <= (~
% 2.56/2.76             (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.56/2.76      inference('split', [status(esa)], ['35'])).
% 2.56/2.76  thf('97', plain,
% 2.56/2.76      (![X0 : $i]:
% 2.56/2.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.56/2.76           = (k4_xboole_0 @ sk_B @ X0))),
% 2.56/2.76      inference('sup-', [status(thm)], ['4', '5'])).
% 2.56/2.76  thf('98', plain,
% 2.56/2.76      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 2.56/2.76         <= (~
% 2.56/2.76             (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 2.56/2.76      inference('demod', [status(thm)], ['96', '97'])).
% 2.56/2.76  thf('99', plain,
% 2.56/2.76      (~
% 2.56/2.76       (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.56/2.76             (k1_tops_1 @ sk_A @ sk_B))))),
% 2.56/2.76      inference('sat_resolution*', [status(thm)], ['36', '69'])).
% 2.56/2.76  thf('100', plain,
% 2.56/2.76      (((k2_tops_1 @ sk_A @ sk_B)
% 2.56/2.76         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.56/2.76      inference('simpl_trail', [status(thm)], ['98', '99'])).
% 2.56/2.76  thf('101', plain, ($false),
% 2.56/2.76      inference('simplify_reflect-', [status(thm)], ['95', '100'])).
% 2.56/2.76  
% 2.56/2.76  % SZS output end Refutation
% 2.56/2.76  
% 2.56/2.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
