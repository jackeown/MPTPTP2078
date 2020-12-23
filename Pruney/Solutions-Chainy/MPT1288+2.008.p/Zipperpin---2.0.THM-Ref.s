%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ed0aRrz7YF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:58 EST 2020

% Result     : Theorem 6.74s
% Output     : Refutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 261 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          : 1241 (3327 expanded)
%              Number of equality atoms :   32 ( 122 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ ( k2_tops_1 @ X20 @ ( k2_tops_1 @ X20 @ X19 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('6',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t94_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_tops_1 @ X28 @ X29 )
      | ( X28
        = ( k2_tops_1 @ X29 @ X28 ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('21',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t96_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X31 @ X30 ) @ X31 )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t96_tops_1])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('32',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29','35'])).

thf('37',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','24','36'])).

thf('38',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t77_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ( ( k2_tops_1 @ X27 @ X26 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k1_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t77_tops_1])).

thf('41',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('45',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_tops_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X21 @ ( k1_tops_1 @ X21 @ X22 ) )
        = ( k1_tops_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('78',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','84'])).

thf('86',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('88',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_tops_1 @ X18 @ X17 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','92'])).

thf('94',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ed0aRrz7YF
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 6.74/6.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.74/6.95  % Solved by: fo/fo7.sh
% 6.74/6.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.74/6.95  % done 6829 iterations in 6.486s
% 6.74/6.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.74/6.95  % SZS output start Refutation
% 6.74/6.95  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 6.74/6.95  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.74/6.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.74/6.95  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 6.74/6.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.74/6.95  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 6.74/6.95  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 6.74/6.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.74/6.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.74/6.95  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 6.74/6.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.74/6.95  thf(sk_A_type, type, sk_A: $i).
% 6.74/6.95  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 6.74/6.95  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 6.74/6.95  thf(sk_B_type, type, sk_B: $i).
% 6.74/6.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.74/6.95  thf(t110_tops_1, conjecture,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ( v4_tops_1 @ B @ A ) =>
% 6.74/6.95             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 6.74/6.95  thf(zf_stmt_0, negated_conjecture,
% 6.74/6.95    (~( ![A:$i]:
% 6.74/6.95        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.74/6.95          ( ![B:$i]:
% 6.74/6.95            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95              ( ( v4_tops_1 @ B @ A ) =>
% 6.74/6.95                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 6.74/6.95    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 6.74/6.95  thf('0', plain,
% 6.74/6.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf(dt_k2_pre_topc, axiom,
% 6.74/6.95    (![A:$i,B:$i]:
% 6.74/6.95     ( ( ( l1_pre_topc @ A ) & 
% 6.74/6.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.74/6.95       ( m1_subset_1 @
% 6.74/6.95         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.74/6.95  thf('1', plain,
% 6.74/6.95      (![X3 : $i, X4 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ X3)
% 6.74/6.95          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 6.74/6.95          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 6.74/6.95             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 6.74/6.95      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 6.74/6.95  thf('2', plain,
% 6.74/6.95      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['0', '1'])).
% 6.74/6.95  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('4', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf(l80_tops_1, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 6.74/6.95             ( k1_xboole_0 ) ) ) ) ))).
% 6.74/6.95  thf('5', plain,
% 6.74/6.95      (![X19 : $i, X20 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 6.74/6.95          | ((k1_tops_1 @ X20 @ (k2_tops_1 @ X20 @ (k2_tops_1 @ X20 @ X19)))
% 6.74/6.95              = (k1_xboole_0))
% 6.74/6.95          | ~ (l1_pre_topc @ X20)
% 6.74/6.95          | ~ (v2_pre_topc @ X20))),
% 6.74/6.95      inference('cnf', [status(esa)], [l80_tops_1])).
% 6.74/6.95  thf('6', plain,
% 6.74/6.95      ((~ (v2_pre_topc @ sk_A)
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A)
% 6.74/6.95        | ((k1_tops_1 @ sk_A @ 
% 6.74/6.95            (k2_tops_1 @ sk_A @ 
% 6.74/6.95             (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 6.74/6.95            = (k1_xboole_0)))),
% 6.74/6.95      inference('sup-', [status(thm)], ['4', '5'])).
% 6.74/6.95  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('9', plain,
% 6.74/6.95      (((k1_tops_1 @ sk_A @ 
% 6.74/6.95         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 6.74/6.95         = (k1_xboole_0))),
% 6.74/6.95      inference('demod', [status(thm)], ['6', '7', '8'])).
% 6.74/6.95  thf('10', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf(dt_k2_tops_1, axiom,
% 6.74/6.95    (![A:$i,B:$i]:
% 6.74/6.95     ( ( ( l1_pre_topc @ A ) & 
% 6.74/6.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.74/6.95       ( m1_subset_1 @
% 6.74/6.95         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.74/6.95  thf('11', plain,
% 6.74/6.95      (![X11 : $i, X12 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ X11)
% 6.74/6.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 6.74/6.95          | (m1_subset_1 @ (k2_tops_1 @ X11 @ X12) @ 
% 6.74/6.95             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 6.74/6.95      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 6.74/6.95  thf('12', plain,
% 6.74/6.95      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['10', '11'])).
% 6.74/6.95  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('14', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['12', '13'])).
% 6.74/6.95  thf(t94_tops_1, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( l1_pre_topc @ A ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ( v4_pre_topc @ B @ A ) =>
% 6.74/6.95             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 6.74/6.95  thf('15', plain,
% 6.74/6.95      (![X28 : $i, X29 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.74/6.95          | ~ (v3_tops_1 @ X28 @ X29)
% 6.74/6.95          | ((X28) = (k2_tops_1 @ X29 @ X28))
% 6.74/6.95          | ~ (v4_pre_topc @ X28 @ X29)
% 6.74/6.95          | ~ (l1_pre_topc @ X29))),
% 6.74/6.95      inference('cnf', [status(esa)], [t94_tops_1])).
% 6.74/6.95  thf('16', plain,
% 6.74/6.95      ((~ (l1_pre_topc @ sk_A)
% 6.74/6.95        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95             sk_A)
% 6.74/6.95        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95            = (k2_tops_1 @ sk_A @ 
% 6.74/6.95               (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 6.74/6.95        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95             sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['14', '15'])).
% 6.74/6.95  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('18', plain,
% 6.74/6.95      ((~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95           sk_A)
% 6.74/6.95        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95            = (k2_tops_1 @ sk_A @ 
% 6.74/6.95               (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 6.74/6.95        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95             sk_A))),
% 6.74/6.95      inference('demod', [status(thm)], ['16', '17'])).
% 6.74/6.95  thf('19', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf(fc11_tops_1, axiom,
% 6.74/6.95    (![A:$i,B:$i]:
% 6.74/6.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 6.74/6.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.74/6.95       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 6.74/6.95  thf('20', plain,
% 6.74/6.95      (![X13 : $i, X14 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ X13)
% 6.74/6.95          | ~ (v2_pre_topc @ X13)
% 6.74/6.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 6.74/6.95          | (v4_pre_topc @ (k2_tops_1 @ X13 @ X14) @ X13))),
% 6.74/6.95      inference('cnf', [status(esa)], [fc11_tops_1])).
% 6.74/6.95  thf('21', plain,
% 6.74/6.95      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)
% 6.74/6.95        | ~ (v2_pre_topc @ sk_A)
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['19', '20'])).
% 6.74/6.95  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('24', plain,
% 6.74/6.95      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)),
% 6.74/6.95      inference('demod', [status(thm)], ['21', '22', '23'])).
% 6.74/6.95  thf('25', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf(t96_tops_1, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ( v4_pre_topc @ B @ A ) =>
% 6.74/6.95             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 6.74/6.95  thf('26', plain,
% 6.74/6.95      (![X30 : $i, X31 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 6.74/6.95          | (v3_tops_1 @ (k2_tops_1 @ X31 @ X30) @ X31)
% 6.74/6.95          | ~ (v4_pre_topc @ X30 @ X31)
% 6.74/6.95          | ~ (l1_pre_topc @ X31)
% 6.74/6.95          | ~ (v2_pre_topc @ X31))),
% 6.74/6.95      inference('cnf', [status(esa)], [t96_tops_1])).
% 6.74/6.95  thf('27', plain,
% 6.74/6.95      ((~ (v2_pre_topc @ sk_A)
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A)
% 6.74/6.95        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 6.74/6.95        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['25', '26'])).
% 6.74/6.95  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('30', plain,
% 6.74/6.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf(fc1_tops_1, axiom,
% 6.74/6.95    (![A:$i,B:$i]:
% 6.74/6.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 6.74/6.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.74/6.95       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 6.74/6.95  thf('31', plain,
% 6.74/6.95      (![X15 : $i, X16 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ X15)
% 6.74/6.95          | ~ (v2_pre_topc @ X15)
% 6.74/6.95          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 6.74/6.95          | (v4_pre_topc @ (k2_pre_topc @ X15 @ X16) @ X15))),
% 6.74/6.95      inference('cnf', [status(esa)], [fc1_tops_1])).
% 6.74/6.95  thf('32', plain,
% 6.74/6.95      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 6.74/6.95        | ~ (v2_pre_topc @ sk_A)
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['30', '31'])).
% 6.74/6.95  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('35', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 6.74/6.95      inference('demod', [status(thm)], ['32', '33', '34'])).
% 6.74/6.95  thf('36', plain,
% 6.74/6.95      ((v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)),
% 6.74/6.95      inference('demod', [status(thm)], ['27', '28', '29', '35'])).
% 6.74/6.95  thf('37', plain,
% 6.74/6.95      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 6.74/6.95      inference('demod', [status(thm)], ['18', '24', '36'])).
% 6.74/6.95  thf('38', plain,
% 6.74/6.95      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.74/6.95         = (k1_xboole_0))),
% 6.74/6.95      inference('demod', [status(thm)], ['9', '37'])).
% 6.74/6.95  thf('39', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf(t77_tops_1, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ( v4_pre_topc @ B @ A ) <=>
% 6.74/6.95             ( ( k2_tops_1 @ A @ B ) =
% 6.74/6.95               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 6.74/6.95  thf('40', plain,
% 6.74/6.95      (![X26 : $i, X27 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 6.74/6.95          | ~ (v4_pre_topc @ X26 @ X27)
% 6.74/6.95          | ((k2_tops_1 @ X27 @ X26)
% 6.74/6.95              = (k7_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 6.74/6.95                 (k1_tops_1 @ X27 @ X26)))
% 6.74/6.95          | ~ (l1_pre_topc @ X27)
% 6.74/6.95          | ~ (v2_pre_topc @ X27))),
% 6.74/6.95      inference('cnf', [status(esa)], [t77_tops_1])).
% 6.74/6.95  thf('41', plain,
% 6.74/6.95      ((~ (v2_pre_topc @ sk_A)
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A)
% 6.74/6.95        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.74/6.95               (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95               (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 6.74/6.95        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['39', '40'])).
% 6.74/6.95  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('44', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 6.74/6.95      inference('demod', [status(thm)], ['32', '33', '34'])).
% 6.74/6.95  thf('45', plain,
% 6.74/6.95      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 6.74/6.95      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 6.74/6.95  thf('46', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf('47', plain,
% 6.74/6.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf(t48_tops_1, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( l1_pre_topc @ A ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ![C:$i]:
% 6.74/6.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95               ( ( r1_tarski @ B @ C ) =>
% 6.74/6.95                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 6.74/6.95  thf('48', plain,
% 6.74/6.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 6.74/6.95          | ~ (r1_tarski @ X23 @ X25)
% 6.74/6.95          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ (k1_tops_1 @ X24 @ X25))
% 6.74/6.95          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 6.74/6.95          | ~ (l1_pre_topc @ X24))),
% 6.74/6.95      inference('cnf', [status(esa)], [t48_tops_1])).
% 6.74/6.95  thf('49', plain,
% 6.74/6.95      (![X0 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ sk_A)
% 6.74/6.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 6.74/6.95          | ~ (r1_tarski @ sk_B @ X0))),
% 6.74/6.95      inference('sup-', [status(thm)], ['47', '48'])).
% 6.74/6.95  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('51', plain,
% 6.74/6.95      (![X0 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 6.74/6.95          | ~ (r1_tarski @ sk_B @ X0))),
% 6.74/6.95      inference('demod', [status(thm)], ['49', '50'])).
% 6.74/6.95  thf('52', plain,
% 6.74/6.95      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.74/6.95           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 6.74/6.95      inference('sup-', [status(thm)], ['46', '51'])).
% 6.74/6.95  thf('53', plain,
% 6.74/6.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf(t48_pre_topc, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( l1_pre_topc @ A ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 6.74/6.95  thf('54', plain,
% 6.74/6.95      (![X5 : $i, X6 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 6.74/6.95          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 6.74/6.95          | ~ (l1_pre_topc @ X6))),
% 6.74/6.95      inference('cnf', [status(esa)], [t48_pre_topc])).
% 6.74/6.95  thf('55', plain,
% 6.74/6.95      ((~ (l1_pre_topc @ sk_A)
% 6.74/6.95        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.74/6.95      inference('sup-', [status(thm)], ['53', '54'])).
% 6.74/6.95  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('57', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 6.74/6.95      inference('demod', [status(thm)], ['55', '56'])).
% 6.74/6.95  thf('58', plain,
% 6.74/6.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.74/6.95      inference('demod', [status(thm)], ['52', '57'])).
% 6.74/6.95  thf(d10_xboole_0, axiom,
% 6.74/6.95    (![A:$i,B:$i]:
% 6.74/6.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.74/6.95  thf('59', plain,
% 6.74/6.95      (![X0 : $i, X2 : $i]:
% 6.74/6.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.74/6.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.74/6.95  thf('60', plain,
% 6.74/6.95      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95           (k1_tops_1 @ sk_A @ sk_B))
% 6.74/6.95        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95            = (k1_tops_1 @ sk_A @ sk_B)))),
% 6.74/6.95      inference('sup-', [status(thm)], ['58', '59'])).
% 6.74/6.95  thf('61', plain,
% 6.74/6.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf(d6_tops_1, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( l1_pre_topc @ A ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ( v4_tops_1 @ B @ A ) <=>
% 6.74/6.95             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 6.74/6.95               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 6.74/6.95  thf('62', plain,
% 6.74/6.95      (![X7 : $i, X8 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 6.74/6.95          | ~ (v4_tops_1 @ X7 @ X8)
% 6.74/6.95          | (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 6.74/6.95          | ~ (l1_pre_topc @ X8))),
% 6.74/6.95      inference('cnf', [status(esa)], [d6_tops_1])).
% 6.74/6.95  thf('63', plain,
% 6.74/6.95      ((~ (l1_pre_topc @ sk_A)
% 6.74/6.95        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 6.74/6.95        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['61', '62'])).
% 6.74/6.95  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('65', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('66', plain,
% 6.74/6.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 6.74/6.95      inference('demod', [status(thm)], ['63', '64', '65'])).
% 6.74/6.95  thf('67', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf(dt_k1_tops_1, axiom,
% 6.74/6.95    (![A:$i,B:$i]:
% 6.74/6.95     ( ( ( l1_pre_topc @ A ) & 
% 6.74/6.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.74/6.95       ( m1_subset_1 @
% 6.74/6.95         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.74/6.95  thf('68', plain,
% 6.74/6.95      (![X9 : $i, X10 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ X9)
% 6.74/6.95          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 6.74/6.95          | (m1_subset_1 @ (k1_tops_1 @ X9 @ X10) @ 
% 6.74/6.95             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 6.74/6.95      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 6.74/6.95  thf('69', plain,
% 6.74/6.95      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['67', '68'])).
% 6.74/6.95  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('71', plain,
% 6.74/6.95      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['69', '70'])).
% 6.74/6.95  thf('72', plain,
% 6.74/6.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 6.74/6.95          | ~ (r1_tarski @ X23 @ X25)
% 6.74/6.95          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ (k1_tops_1 @ X24 @ X25))
% 6.74/6.95          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 6.74/6.95          | ~ (l1_pre_topc @ X24))),
% 6.74/6.95      inference('cnf', [status(esa)], [t48_tops_1])).
% 6.74/6.95  thf('73', plain,
% 6.74/6.95      (![X0 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ sk_A)
% 6.74/6.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95          | (r1_tarski @ 
% 6.74/6.95             (k1_tops_1 @ sk_A @ 
% 6.74/6.95              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 6.74/6.95             (k1_tops_1 @ sk_A @ X0))
% 6.74/6.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95               X0))),
% 6.74/6.95      inference('sup-', [status(thm)], ['71', '72'])).
% 6.74/6.95  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('75', plain,
% 6.74/6.95      (![X0 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95          | (r1_tarski @ 
% 6.74/6.95             (k1_tops_1 @ sk_A @ 
% 6.74/6.95              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 6.74/6.95             (k1_tops_1 @ sk_A @ X0))
% 6.74/6.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95               X0))),
% 6.74/6.95      inference('demod', [status(thm)], ['73', '74'])).
% 6.74/6.95  thf('76', plain,
% 6.74/6.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('demod', [status(thm)], ['2', '3'])).
% 6.74/6.95  thf(projectivity_k1_tops_1, axiom,
% 6.74/6.95    (![A:$i,B:$i]:
% 6.74/6.95     ( ( ( l1_pre_topc @ A ) & 
% 6.74/6.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.74/6.95       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 6.74/6.95  thf('77', plain,
% 6.74/6.95      (![X21 : $i, X22 : $i]:
% 6.74/6.95         (~ (l1_pre_topc @ X21)
% 6.74/6.95          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 6.74/6.95          | ((k1_tops_1 @ X21 @ (k1_tops_1 @ X21 @ X22))
% 6.74/6.95              = (k1_tops_1 @ X21 @ X22)))),
% 6.74/6.95      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 6.74/6.95  thf('78', plain,
% 6.74/6.95      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.74/6.95          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.74/6.95        | ~ (l1_pre_topc @ sk_A))),
% 6.74/6.95      inference('sup-', [status(thm)], ['76', '77'])).
% 6.74/6.95  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('80', plain,
% 6.74/6.95      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.74/6.95         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.74/6.95      inference('demod', [status(thm)], ['78', '79'])).
% 6.74/6.95  thf('81', plain,
% 6.74/6.95      (![X0 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.74/6.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95             (k1_tops_1 @ sk_A @ X0))
% 6.74/6.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95               X0))),
% 6.74/6.95      inference('demod', [status(thm)], ['75', '80'])).
% 6.74/6.95  thf('82', plain,
% 6.74/6.95      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95         (k1_tops_1 @ sk_A @ sk_B))
% 6.74/6.95        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.74/6.95      inference('sup-', [status(thm)], ['66', '81'])).
% 6.74/6.95  thf('83', plain,
% 6.74/6.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('84', plain,
% 6.74/6.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.74/6.95        (k1_tops_1 @ sk_A @ sk_B))),
% 6.74/6.95      inference('demod', [status(thm)], ['82', '83'])).
% 6.74/6.95  thf('85', plain,
% 6.74/6.95      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95         = (k1_tops_1 @ sk_A @ sk_B))),
% 6.74/6.95      inference('demod', [status(thm)], ['60', '84'])).
% 6.74/6.95  thf('86', plain,
% 6.74/6.95      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.74/6.95         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95            (k1_tops_1 @ sk_A @ sk_B)))),
% 6.74/6.95      inference('demod', [status(thm)], ['45', '85'])).
% 6.74/6.95  thf('87', plain,
% 6.74/6.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf(l78_tops_1, axiom,
% 6.74/6.95    (![A:$i]:
% 6.74/6.95     ( ( l1_pre_topc @ A ) =>
% 6.74/6.95       ( ![B:$i]:
% 6.74/6.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.74/6.95           ( ( k2_tops_1 @ A @ B ) =
% 6.74/6.95             ( k7_subset_1 @
% 6.74/6.95               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 6.74/6.95               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 6.74/6.95  thf('88', plain,
% 6.74/6.95      (![X17 : $i, X18 : $i]:
% 6.74/6.95         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 6.74/6.95          | ((k2_tops_1 @ X18 @ X17)
% 6.74/6.95              = (k7_subset_1 @ (u1_struct_0 @ X18) @ 
% 6.74/6.95                 (k2_pre_topc @ X18 @ X17) @ (k1_tops_1 @ X18 @ X17)))
% 6.74/6.95          | ~ (l1_pre_topc @ X18))),
% 6.74/6.95      inference('cnf', [status(esa)], [l78_tops_1])).
% 6.74/6.95  thf('89', plain,
% 6.74/6.95      ((~ (l1_pre_topc @ sk_A)
% 6.74/6.95        | ((k2_tops_1 @ sk_A @ sk_B)
% 6.74/6.95            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.74/6.95               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 6.74/6.95      inference('sup-', [status(thm)], ['87', '88'])).
% 6.74/6.95  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('91', plain,
% 6.74/6.95      (((k2_tops_1 @ sk_A @ sk_B)
% 6.74/6.95         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.74/6.95            (k1_tops_1 @ sk_A @ sk_B)))),
% 6.74/6.95      inference('demod', [status(thm)], ['89', '90'])).
% 6.74/6.95  thf('92', plain,
% 6.74/6.95      (((k2_tops_1 @ sk_A @ sk_B)
% 6.74/6.95         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.74/6.95      inference('sup+', [status(thm)], ['86', '91'])).
% 6.74/6.95  thf('93', plain,
% 6.74/6.95      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 6.74/6.95      inference('demod', [status(thm)], ['38', '92'])).
% 6.74/6.95  thf('94', plain,
% 6.74/6.95      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 6.74/6.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.74/6.95  thf('95', plain, ($false),
% 6.74/6.95      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 6.74/6.95  
% 6.74/6.95  % SZS output end Refutation
% 6.74/6.95  
% 6.74/6.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
