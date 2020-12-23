%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QCv9RTU6Pf

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:16 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 671 expanded)
%              Number of leaves         :   30 ( 197 expanded)
%              Depth                    :   22
%              Number of atoms          : 1190 (9361 expanded)
%              Number of equality atoms :   63 ( 428 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( r1_tarski @ X31 @ X33 )
      | ( r1_tarski @ ( k1_tops_1 @ X32 @ X31 ) @ ( k1_tops_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( ( k1_tops_1 @ X34 @ X35 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('11',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
        | ~ ( v3_pre_topc @ X35 @ X34 )
        | ( ( k1_tops_1 @ X34 @ X35 )
          = X35 ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
        | ~ ( v3_pre_topc @ X35 @ X34 )
        | ( ( k1_tops_1 @ X34 @ X35 )
          = X35 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( ( k1_tops_1 @ X34 @ X35 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('14',plain,
    ( ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) )
   <= ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( l1_pre_topc @ X34 )
        | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
        | ~ ( v3_pre_topc @ X35 @ X34 )
        | ( ( k1_tops_1 @ X34 @ X35 )
          = X35 ) )
    | ! [X36: $i,X37: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( l1_pre_topc @ X37 )
        | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( ( k1_tops_1 @ X34 @ X35 )
        = X35 ) ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v3_pre_topc @ X35 @ X34 )
      | ( ( k1_tops_1 @ X34 @ X35 )
        = X35 ) ) ),
    inference(simpl_trail,[status(thm)],['11','20'])).

thf('22',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X40 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X40 @ sk_A )
      | ~ ( r1_tarski @ X40 @ sk_B_2 )
      | ( v2_tops_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_tops_1 @ sk_B_2 @ sk_A )
    | ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_B_2 ),
    inference(demod,[status(thm)],['30','31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_B_2 )
    = ( k1_tops_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ ( k1_tops_1 @ sk_A @ sk_B_2 ) )
    = ( k1_tops_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','39'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B_2 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X40 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X40 @ sk_A )
      | ~ ( r1_tarski @ X40 @ sk_B_2 )
      | ( v2_tops_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B_2 ) )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_B_2 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_2 )
        = k1_xboole_0 ) )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_B_2 ),
    inference(demod,[status(thm)],['30','31'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('56',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('57',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['53','54','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('63',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ X38 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_2 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_2 @ sk_A ) )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( v2_tops_1 @ sk_B_2 @ sk_A )
   <= ! [X40: $i] :
        ( ( X40 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X40 @ sk_A )
        | ~ ( r1_tarski @ X40 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_C @ sk_B_2 )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v2_tops_1 @ sk_B_2 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ~ ! [X40: $i] :
          ( ( X40 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X40 @ sk_A )
          | ~ ( r1_tarski @ X40 @ sk_B_2 ) )
    | ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('73',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','71','72'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','71','74'])).

thf('76',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['25','73','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','71','74'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_2 )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','79'])).

thf('81',plain,
    ( ( r1_tarski @ sk_C @ sk_B_2 )
   <= ( r1_tarski @ sk_C @ sk_B_2 ) ),
    inference(split,[status(esa)],['69'])).

thf('82',plain,
    ( ( r1_tarski @ sk_C @ sk_B_2 )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['69'])).

thf('83',plain,(
    r1_tarski @ sk_C @ sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['27','71','82'])).

thf('84',plain,(
    r1_tarski @ sk_C @ sk_B_2 ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,
    ( ( v2_tops_1 @ sk_B_2 @ sk_A )
   <= ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_tops_1 @ X38 @ X39 )
      | ( ( k1_tops_1 @ X39 @ X38 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    v2_tops_1 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','71'])).

thf('93',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['80','84','93'])).

thf('95',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('96',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('97',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('98',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['96','101'])).

thf('103',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['103'])).

thf('106',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['27','71','105'])).

thf('107',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['104','106'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QCv9RTU6Pf
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:29:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 1330 iterations in 0.381s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.81  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.59/0.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.81  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.59/0.81  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.81  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.59/0.81  thf(t86_tops_1, conjecture,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ( v2_tops_1 @ B @ A ) <=>
% 0.59/0.81             ( ![C:$i]:
% 0.59/0.81               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.59/0.81                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i]:
% 0.59/0.81        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.81          ( ![B:$i]:
% 0.59/0.81            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81              ( ( v2_tops_1 @ B @ A ) <=>
% 0.59/0.81                ( ![C:$i]:
% 0.59/0.81                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.59/0.81                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.59/0.81  thf('0', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('1', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81        | ~ (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.81      inference('split', [status(esa)], ['1'])).
% 0.59/0.81  thf(t48_tops_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ![C:$i]:
% 0.59/0.81             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81               ( ( r1_tarski @ B @ C ) =>
% 0.59/0.81                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.59/0.81          | ~ (r1_tarski @ X31 @ X33)
% 0.59/0.81          | (r1_tarski @ (k1_tops_1 @ X32 @ X31) @ (k1_tops_1 @ X32 @ X33))
% 0.59/0.81          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.59/0.81          | ~ (l1_pre_topc @ X32))),
% 0.59/0.81      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.59/0.81  thf('4', plain,
% 0.59/0.81      ((![X0 : $i]:
% 0.59/0.81          (~ (l1_pre_topc @ sk_A)
% 0.59/0.81           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.81           | ~ (r1_tarski @ sk_C @ X0)))
% 0.59/0.81         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.81  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      ((![X0 : $i]:
% 0.59/0.81          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.81           | ~ (r1_tarski @ sk_C @ X0)))
% 0.59/0.81         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.81      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.59/0.81      inference('split', [status(esa)], ['7'])).
% 0.59/0.81  thf('9', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.81      inference('split', [status(esa)], ['1'])).
% 0.59/0.81  thf(t55_tops_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( l1_pre_topc @ B ) =>
% 0.59/0.81           ( ![C:$i]:
% 0.59/0.81             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81               ( ![D:$i]:
% 0.59/0.81                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.59/0.81                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.59/0.81                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.59/0.81                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.59/0.81                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.81  thf('10', plain,
% 0.59/0.81      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X34)
% 0.59/0.81          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.59/0.81          | ~ (v3_pre_topc @ X35 @ X34)
% 0.59/0.81          | ((k1_tops_1 @ X34 @ X35) = (X35))
% 0.59/0.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.59/0.81          | ~ (l1_pre_topc @ X37)
% 0.59/0.81          | ~ (v2_pre_topc @ X37))),
% 0.59/0.81      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      ((![X34 : $i, X35 : $i]:
% 0.59/0.81          (~ (l1_pre_topc @ X34)
% 0.59/0.81           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.59/0.81           | ~ (v3_pre_topc @ X35 @ X34)
% 0.59/0.81           | ((k1_tops_1 @ X34 @ X35) = (X35))))
% 0.59/0.81         <= ((![X34 : $i, X35 : $i]:
% 0.59/0.81                (~ (l1_pre_topc @ X34)
% 0.59/0.81                 | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.59/0.81                 | ~ (v3_pre_topc @ X35 @ X34)
% 0.59/0.81                 | ((k1_tops_1 @ X34 @ X35) = (X35)))))),
% 0.59/0.81      inference('split', [status(esa)], ['10'])).
% 0.59/0.81  thf('12', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X34)
% 0.59/0.81          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.59/0.81          | ~ (v3_pre_topc @ X35 @ X34)
% 0.59/0.81          | ((k1_tops_1 @ X34 @ X35) = (X35))
% 0.59/0.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.59/0.81          | ~ (l1_pre_topc @ X37)
% 0.59/0.81          | ~ (v2_pre_topc @ X37))),
% 0.59/0.81      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      ((![X36 : $i, X37 : $i]:
% 0.59/0.81          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.59/0.81           | ~ (l1_pre_topc @ X37)
% 0.59/0.81           | ~ (v2_pre_topc @ X37)))
% 0.59/0.81         <= ((![X36 : $i, X37 : $i]:
% 0.59/0.81                (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.59/0.81                 | ~ (l1_pre_topc @ X37)
% 0.59/0.81                 | ~ (v2_pre_topc @ X37))))),
% 0.59/0.81      inference('split', [status(esa)], ['13'])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.59/0.81         <= ((![X36 : $i, X37 : $i]:
% 0.59/0.81                (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.59/0.81                 | ~ (l1_pre_topc @ X37)
% 0.59/0.81                 | ~ (v2_pre_topc @ X37))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['12', '14'])).
% 0.59/0.81  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('18', plain,
% 0.59/0.81      (~
% 0.59/0.81       (![X36 : $i, X37 : $i]:
% 0.59/0.81          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.59/0.81           | ~ (l1_pre_topc @ X37)
% 0.59/0.81           | ~ (v2_pre_topc @ X37)))),
% 0.59/0.81      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.59/0.81  thf('19', plain,
% 0.59/0.81      ((![X34 : $i, X35 : $i]:
% 0.59/0.81          (~ (l1_pre_topc @ X34)
% 0.59/0.81           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.59/0.81           | ~ (v3_pre_topc @ X35 @ X34)
% 0.59/0.81           | ((k1_tops_1 @ X34 @ X35) = (X35)))) | 
% 0.59/0.81       (![X36 : $i, X37 : $i]:
% 0.59/0.81          (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.59/0.81           | ~ (l1_pre_topc @ X37)
% 0.59/0.81           | ~ (v2_pre_topc @ X37)))),
% 0.59/0.81      inference('split', [status(esa)], ['13'])).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      ((![X34 : $i, X35 : $i]:
% 0.59/0.81          (~ (l1_pre_topc @ X34)
% 0.59/0.81           | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.59/0.81           | ~ (v3_pre_topc @ X35 @ X34)
% 0.59/0.81           | ((k1_tops_1 @ X34 @ X35) = (X35))))),
% 0.59/0.81      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.59/0.81  thf('21', plain,
% 0.59/0.81      (![X34 : $i, X35 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X34)
% 0.59/0.81          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.59/0.81          | ~ (v3_pre_topc @ X35 @ X34)
% 0.59/0.81          | ((k1_tops_1 @ X34 @ X35) = (X35)))),
% 0.59/0.81      inference('simpl_trail', [status(thm)], ['11', '20'])).
% 0.59/0.81  thf('22', plain,
% 0.59/0.81      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.59/0.81         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.59/0.81         | ~ (l1_pre_topc @ sk_A)))
% 0.59/0.81         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['9', '21'])).
% 0.59/0.81  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('24', plain,
% 0.59/0.81      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.59/0.81         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.81      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.59/0.81         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.59/0.81             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['8', '24'])).
% 0.59/0.81  thf('26', plain,
% 0.59/0.81      (![X40 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81          | ((X40) = (k1_xboole_0))
% 0.59/0.81          | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.81          | ~ (r1_tarski @ X40 @ sk_B_2)
% 0.59/0.81          | (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('27', plain,
% 0.59/0.81      (((v2_tops_1 @ sk_B_2 @ sk_A)) | 
% 0.59/0.81       (![X40 : $i]:
% 0.59/0.81          (((X40) = (k1_xboole_0))
% 0.59/0.81           | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81           | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.81           | ~ (r1_tarski @ X40 @ sk_B_2)))),
% 0.59/0.81      inference('split', [status(esa)], ['26'])).
% 0.59/0.81  thf('28', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(t44_tops_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      (![X29 : $i, X30 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.59/0.81          | (r1_tarski @ (k1_tops_1 @ X30 @ X29) @ X29)
% 0.59/0.81          | ~ (l1_pre_topc @ X30))),
% 0.59/0.81      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_B_2))),
% 0.59/0.81      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.81  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('32', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_B_2)),
% 0.59/0.81      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.81  thf(t28_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      (![X8 : $i, X9 : $i]:
% 0.59/0.81         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_B_2)
% 0.59/0.81         = (k1_tops_1 @ sk_A @ sk_B_2))),
% 0.59/0.81      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.81  thf(commutativity_k2_tarski, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.59/0.81  thf('35', plain,
% 0.59/0.81      (![X13 : $i, X14 : $i]:
% 0.59/0.81         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 0.59/0.81      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.59/0.81  thf(t12_setfam_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.82  thf('36', plain,
% 0.59/0.82      (![X15 : $i, X16 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.82  thf('37', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('sup+', [status(thm)], ['35', '36'])).
% 0.59/0.82  thf('38', plain,
% 0.59/0.82      (![X15 : $i, X16 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.59/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.82  thf('39', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('sup+', [status(thm)], ['37', '38'])).
% 0.59/0.82  thf('40', plain,
% 0.59/0.82      (((k3_xboole_0 @ sk_B_2 @ (k1_tops_1 @ sk_A @ sk_B_2))
% 0.59/0.82         = (k1_tops_1 @ sk_A @ sk_B_2))),
% 0.59/0.82      inference('demod', [status(thm)], ['34', '39'])).
% 0.59/0.82  thf(t48_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.82  thf('41', plain,
% 0.59/0.82      (![X11 : $i, X12 : $i]:
% 0.59/0.82         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.59/0.82           = (k3_xboole_0 @ X11 @ X12))),
% 0.59/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.82  thf('42', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t3_subset, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.82  thf('43', plain,
% 0.59/0.82      (![X17 : $i, X18 : $i]:
% 0.59/0.82         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.82  thf('44', plain, ((r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.82  thf(t109_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.59/0.82  thf('45', plain,
% 0.59/0.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.82         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 0.59/0.82      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.59/0.82  thf('46', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (r1_tarski @ (k4_xboole_0 @ sk_B_2 @ X0) @ (u1_struct_0 @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['44', '45'])).
% 0.59/0.82  thf('47', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (r1_tarski @ (k3_xboole_0 @ sk_B_2 @ X0) @ (u1_struct_0 @ sk_A))),
% 0.59/0.82      inference('sup+', [status(thm)], ['41', '46'])).
% 0.59/0.82  thf('48', plain,
% 0.59/0.82      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 0.59/0.82      inference('sup+', [status(thm)], ['40', '47'])).
% 0.59/0.82  thf('49', plain,
% 0.59/0.82      (![X17 : $i, X19 : $i]:
% 0.59/0.82         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.59/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.82  thf('50', plain,
% 0.59/0.82      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_2) @ 
% 0.59/0.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.82  thf('51', plain,
% 0.59/0.82      (![X40 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82          | ((X40) = (k1_xboole_0))
% 0.59/0.82          | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82          | ~ (r1_tarski @ X40 @ sk_B_2)
% 0.59/0.82          | (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('52', plain,
% 0.59/0.82      ((![X40 : $i]:
% 0.59/0.82          (((X40) = (k1_xboole_0))
% 0.59/0.82           | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82           | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82           | ~ (r1_tarski @ X40 @ sk_B_2)))
% 0.59/0.82         <= ((![X40 : $i]:
% 0.59/0.82                (((X40) = (k1_xboole_0))
% 0.59/0.82                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82                 | ~ (r1_tarski @ X40 @ sk_B_2))))),
% 0.59/0.82      inference('split', [status(esa)], ['51'])).
% 0.59/0.82  thf('53', plain,
% 0.59/0.82      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_B_2)
% 0.59/0.82         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_A)
% 0.59/0.82         | ((k1_tops_1 @ sk_A @ sk_B_2) = (k1_xboole_0))))
% 0.59/0.82         <= ((![X40 : $i]:
% 0.59/0.82                (((X40) = (k1_xboole_0))
% 0.59/0.82                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82                 | ~ (r1_tarski @ X40 @ sk_B_2))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['50', '52'])).
% 0.59/0.82  thf('54', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_B_2)),
% 0.59/0.82      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.82  thf('55', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(fc9_tops_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.59/0.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.82       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.59/0.82  thf('56', plain,
% 0.59/0.82      (![X26 : $i, X27 : $i]:
% 0.59/0.82         (~ (l1_pre_topc @ X26)
% 0.59/0.82          | ~ (v2_pre_topc @ X26)
% 0.59/0.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.59/0.82          | (v3_pre_topc @ (k1_tops_1 @ X26 @ X27) @ X26))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.59/0.82  thf('57', plain,
% 0.59/0.82      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_A)
% 0.59/0.82        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.82        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['55', '56'])).
% 0.59/0.82  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('60', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.59/0.82      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.59/0.82  thf('61', plain,
% 0.59/0.82      ((((k1_tops_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))
% 0.59/0.82         <= ((![X40 : $i]:
% 0.59/0.82                (((X40) = (k1_xboole_0))
% 0.59/0.82                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82                 | ~ (r1_tarski @ X40 @ sk_B_2))))),
% 0.59/0.82      inference('demod', [status(thm)], ['53', '54', '60'])).
% 0.59/0.82  thf('62', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t84_tops_1, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( l1_pre_topc @ A ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.82           ( ( v2_tops_1 @ B @ A ) <=>
% 0.59/0.82             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.59/0.82  thf('63', plain,
% 0.59/0.82      (![X38 : $i, X39 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.59/0.82          | ((k1_tops_1 @ X39 @ X38) != (k1_xboole_0))
% 0.59/0.82          | (v2_tops_1 @ X38 @ X39)
% 0.59/0.82          | ~ (l1_pre_topc @ X39))),
% 0.59/0.82      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.59/0.82  thf('64', plain,
% 0.59/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.82        | (v2_tops_1 @ sk_B_2 @ sk_A)
% 0.59/0.82        | ((k1_tops_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['62', '63'])).
% 0.59/0.82  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('66', plain,
% 0.59/0.82      (((v2_tops_1 @ sk_B_2 @ sk_A)
% 0.59/0.82        | ((k1_tops_1 @ sk_A @ sk_B_2) != (k1_xboole_0)))),
% 0.59/0.82      inference('demod', [status(thm)], ['64', '65'])).
% 0.59/0.82  thf('67', plain,
% 0.59/0.82      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_2 @ sk_A)))
% 0.59/0.82         <= ((![X40 : $i]:
% 0.59/0.82                (((X40) = (k1_xboole_0))
% 0.59/0.82                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82                 | ~ (r1_tarski @ X40 @ sk_B_2))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['61', '66'])).
% 0.59/0.82  thf('68', plain,
% 0.59/0.82      (((v2_tops_1 @ sk_B_2 @ sk_A))
% 0.59/0.82         <= ((![X40 : $i]:
% 0.59/0.82                (((X40) = (k1_xboole_0))
% 0.59/0.82                 | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82                 | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82                 | ~ (r1_tarski @ X40 @ sk_B_2))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['67'])).
% 0.59/0.82  thf('69', plain,
% 0.59/0.82      (((r1_tarski @ sk_C @ sk_B_2) | ~ (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('70', plain,
% 0.59/0.82      ((~ (v2_tops_1 @ sk_B_2 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_2 @ sk_A)))),
% 0.59/0.82      inference('split', [status(esa)], ['69'])).
% 0.59/0.82  thf('71', plain,
% 0.59/0.82      (~
% 0.59/0.82       (![X40 : $i]:
% 0.59/0.82          (((X40) = (k1_xboole_0))
% 0.59/0.82           | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82           | ~ (v3_pre_topc @ X40 @ sk_A)
% 0.59/0.82           | ~ (r1_tarski @ X40 @ sk_B_2))) | 
% 0.59/0.82       ((v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['68', '70'])).
% 0.59/0.82  thf('72', plain,
% 0.59/0.82      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('split', [status(esa)], ['7'])).
% 0.59/0.82  thf('73', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['27', '71', '72'])).
% 0.59/0.82  thf('74', plain,
% 0.59/0.82      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.59/0.82       ~ ((v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('split', [status(esa)], ['1'])).
% 0.59/0.82  thf('75', plain,
% 0.59/0.82      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['27', '71', '74'])).
% 0.59/0.82  thf('76', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['25', '73', '75'])).
% 0.59/0.82  thf('77', plain,
% 0.59/0.82      ((![X0 : $i]:
% 0.59/0.82          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.82           | ~ (r1_tarski @ sk_C @ X0)))
% 0.59/0.82         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.82      inference('demod', [status(thm)], ['6', '76'])).
% 0.59/0.82  thf('78', plain,
% 0.59/0.82      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['27', '71', '74'])).
% 0.59/0.82  thf('79', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.82          | ~ (r1_tarski @ sk_C @ X0))),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 0.59/0.82  thf('80', plain,
% 0.59/0.82      ((~ (r1_tarski @ sk_C @ sk_B_2)
% 0.59/0.82        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B_2)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['0', '79'])).
% 0.59/0.82  thf('81', plain,
% 0.59/0.82      (((r1_tarski @ sk_C @ sk_B_2)) <= (((r1_tarski @ sk_C @ sk_B_2)))),
% 0.59/0.82      inference('split', [status(esa)], ['69'])).
% 0.59/0.82  thf('82', plain,
% 0.59/0.82      (((r1_tarski @ sk_C @ sk_B_2)) | ~ ((v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('split', [status(esa)], ['69'])).
% 0.59/0.82  thf('83', plain, (((r1_tarski @ sk_C @ sk_B_2))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['27', '71', '82'])).
% 0.59/0.82  thf('84', plain, ((r1_tarski @ sk_C @ sk_B_2)),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 0.59/0.82  thf('85', plain,
% 0.59/0.82      (((v2_tops_1 @ sk_B_2 @ sk_A)) <= (((v2_tops_1 @ sk_B_2 @ sk_A)))),
% 0.59/0.82      inference('split', [status(esa)], ['26'])).
% 0.59/0.82  thf('86', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('87', plain,
% 0.59/0.82      (![X38 : $i, X39 : $i]:
% 0.59/0.82         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.59/0.82          | ~ (v2_tops_1 @ X38 @ X39)
% 0.59/0.82          | ((k1_tops_1 @ X39 @ X38) = (k1_xboole_0))
% 0.59/0.82          | ~ (l1_pre_topc @ X39))),
% 0.59/0.82      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.59/0.82  thf('88', plain,
% 0.59/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.82        | ((k1_tops_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.59/0.82        | ~ (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['86', '87'])).
% 0.59/0.82  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('90', plain,
% 0.59/0.82      ((((k1_tops_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.59/0.82        | ~ (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('demod', [status(thm)], ['88', '89'])).
% 0.59/0.82  thf('91', plain,
% 0.59/0.82      ((((k1_tops_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))
% 0.59/0.82         <= (((v2_tops_1 @ sk_B_2 @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['85', '90'])).
% 0.59/0.82  thf('92', plain, (((v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['27', '71'])).
% 0.59/0.82  thf('93', plain, (((k1_tops_1 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.59/0.82  thf('94', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.59/0.82      inference('demod', [status(thm)], ['80', '84', '93'])).
% 0.59/0.82  thf('95', plain,
% 0.59/0.82      (![X8 : $i, X9 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.59/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.82  thf('96', plain, (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (sk_C))),
% 0.59/0.82      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.82  thf('97', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.59/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.82  thf('98', plain,
% 0.59/0.82      (![X8 : $i, X9 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.59/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.82  thf('99', plain,
% 0.59/0.82      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['97', '98'])).
% 0.59/0.82  thf('100', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('sup+', [status(thm)], ['37', '38'])).
% 0.59/0.82  thf('101', plain,
% 0.59/0.82      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.82      inference('sup+', [status(thm)], ['99', '100'])).
% 0.59/0.82  thf('102', plain, (((k1_xboole_0) = (sk_C))),
% 0.59/0.82      inference('demod', [status(thm)], ['96', '101'])).
% 0.59/0.82  thf('103', plain,
% 0.59/0.82      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('104', plain,
% 0.59/0.82      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.59/0.82      inference('split', [status(esa)], ['103'])).
% 0.59/0.82  thf('105', plain,
% 0.59/0.82      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_2 @ sk_A))),
% 0.59/0.82      inference('split', [status(esa)], ['103'])).
% 0.59/0.82  thf('106', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['27', '71', '105'])).
% 0.59/0.82  thf('107', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['104', '106'])).
% 0.59/0.82  thf('108', plain, ($false),
% 0.59/0.82      inference('simplify_reflect-', [status(thm)], ['102', '107'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
