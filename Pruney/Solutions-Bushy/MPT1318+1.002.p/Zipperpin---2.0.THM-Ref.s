%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1318+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y4EQIfpXyI

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:29 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   64 (  92 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  470 (1008 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t38_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_tops_2])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X2
       != ( k1_pre_topc @ X1 @ X0 ) )
      | ( ( k2_struct_0 @ X2 )
        = X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) @ X1 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('13',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X3 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('19',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['16','21'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['22','30'])).

thf('32',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('37',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['4','39'])).


%------------------------------------------------------------------------------
