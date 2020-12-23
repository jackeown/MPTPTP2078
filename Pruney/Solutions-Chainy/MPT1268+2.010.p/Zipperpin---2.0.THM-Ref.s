%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n0mnanwxb1

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:17 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 617 expanded)
%              Number of leaves         :   30 ( 179 expanded)
%              Depth                    :   21
%              Number of atoms          : 1159 (8942 expanded)
%              Number of equality atoms :   58 ( 376 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( r1_tarski @ X29 @ X31 )
      | ( r1_tarski @ ( k1_tops_1 @ X30 @ X29 ) @ ( k1_tops_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('11',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('14',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) )
    | ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 ) ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 ) ) ),
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
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X38 @ sk_A )
      | ~ ( r1_tarski @ X38 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X38 @ sk_A )
        | ~ ( r1_tarski @ X38 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
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
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,
    ( ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X38 @ sk_A )
        | ~ ( r1_tarski @ X38 @ sk_B_1 ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X38 @ sk_A )
        | ~ ( r1_tarski @ X38 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('46',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X38 @ sk_A )
        | ~ ( r1_tarski @ X38 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('50',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X38 @ sk_A )
        | ~ ( r1_tarski @ X38 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['46','47','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('56',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X38 @ sk_A )
        | ~ ( r1_tarski @ X38 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X38 @ sk_A )
        | ~ ( r1_tarski @ X38 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ~ ! [X38: $i] :
          ( ( X38 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X38 @ sk_A )
          | ~ ( r1_tarski @ X38 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('66',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','64','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','64','67'])).

thf('69',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['25','66','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','64','67'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','72'])).

thf('74',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['62'])).

thf('75',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('76',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['27','64','75'])).

thf('77',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['74','76'])).

thf('78',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v2_tops_1 @ X36 @ X37 )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','64'])).

thf('86',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['84','85'])).

thf('87',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['73','77','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
    = sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('90',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('91',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('93',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('94',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['89','98'])).

thf('100',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['100'])).

thf('102',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['100'])).

thf('103',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['27','64','102'])).

thf('104',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['101','103'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['99','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n0mnanwxb1
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 931 iterations in 0.262s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.49/0.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.49/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.49/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(t86_tops_1, conjecture,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72           ( ( v2_tops_1 @ B @ A ) <=>
% 0.49/0.72             ( ![C:$i]:
% 0.49/0.72               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.49/0.72                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i]:
% 0.49/0.72        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.72          ( ![B:$i]:
% 0.49/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72              ( ( v2_tops_1 @ B @ A ) <=>
% 0.49/0.72                ( ![C:$i]:
% 0.49/0.72                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.49/0.72                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.49/0.72         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('split', [status(esa)], ['1'])).
% 0.49/0.72  thf(t48_tops_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( l1_pre_topc @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72           ( ![C:$i]:
% 0.49/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72               ( ( r1_tarski @ B @ C ) =>
% 0.49/0.72                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.49/0.72          | ~ (r1_tarski @ X29 @ X31)
% 0.49/0.72          | (r1_tarski @ (k1_tops_1 @ X30 @ X29) @ (k1_tops_1 @ X30 @ X31))
% 0.49/0.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.49/0.72          | ~ (l1_pre_topc @ X30))),
% 0.49/0.72      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (l1_pre_topc @ sk_A)
% 0.49/0.72           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.49/0.72           | ~ (r1_tarski @ sk_C @ X0)))
% 0.49/0.72         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.49/0.72           | ~ (r1_tarski @ sk_C @ X0)))
% 0.49/0.72         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['7'])).
% 0.49/0.72  thf('9', plain,
% 0.49/0.72      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.49/0.72         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('split', [status(esa)], ['1'])).
% 0.49/0.72  thf(t55_tops_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( l1_pre_topc @ B ) =>
% 0.49/0.72           ( ![C:$i]:
% 0.49/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72               ( ![D:$i]:
% 0.49/0.72                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.49/0.72                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.49/0.72                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.49/0.72                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.49/0.72                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.72  thf('10', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.49/0.72         (~ (l1_pre_topc @ X32)
% 0.49/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.72          | ~ (v3_pre_topc @ X33 @ X32)
% 0.49/0.72          | ((k1_tops_1 @ X32 @ X33) = (X33))
% 0.49/0.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.72          | ~ (l1_pre_topc @ X35)
% 0.49/0.72          | ~ (v2_pre_topc @ X35))),
% 0.49/0.72      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      ((![X32 : $i, X33 : $i]:
% 0.49/0.72          (~ (l1_pre_topc @ X32)
% 0.49/0.72           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.72           | ~ (v3_pre_topc @ X33 @ X32)
% 0.49/0.72           | ((k1_tops_1 @ X32 @ X33) = (X33))))
% 0.49/0.72         <= ((![X32 : $i, X33 : $i]:
% 0.49/0.72                (~ (l1_pre_topc @ X32)
% 0.49/0.72                 | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.72                 | ~ (v3_pre_topc @ X33 @ X32)
% 0.49/0.72                 | ((k1_tops_1 @ X32 @ X33) = (X33)))))),
% 0.49/0.72      inference('split', [status(esa)], ['10'])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.49/0.72         (~ (l1_pre_topc @ X32)
% 0.49/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.72          | ~ (v3_pre_topc @ X33 @ X32)
% 0.49/0.72          | ((k1_tops_1 @ X32 @ X33) = (X33))
% 0.49/0.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.72          | ~ (l1_pre_topc @ X35)
% 0.49/0.72          | ~ (v2_pre_topc @ X35))),
% 0.49/0.72      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      ((![X34 : $i, X35 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.72           | ~ (l1_pre_topc @ X35)
% 0.49/0.72           | ~ (v2_pre_topc @ X35)))
% 0.49/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.49/0.72                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.72                 | ~ (l1_pre_topc @ X35)
% 0.49/0.72                 | ~ (v2_pre_topc @ X35))))),
% 0.49/0.72      inference('split', [status(esa)], ['13'])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.49/0.72         <= ((![X34 : $i, X35 : $i]:
% 0.49/0.72                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.72                 | ~ (l1_pre_topc @ X35)
% 0.49/0.72                 | ~ (v2_pre_topc @ X35))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['12', '14'])).
% 0.49/0.72  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      (~
% 0.49/0.72       (![X34 : $i, X35 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.72           | ~ (l1_pre_topc @ X35)
% 0.49/0.72           | ~ (v2_pre_topc @ X35)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.49/0.72  thf('19', plain,
% 0.49/0.72      ((![X32 : $i, X33 : $i]:
% 0.49/0.72          (~ (l1_pre_topc @ X32)
% 0.49/0.72           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.72           | ~ (v3_pre_topc @ X33 @ X32)
% 0.49/0.72           | ((k1_tops_1 @ X32 @ X33) = (X33)))) | 
% 0.49/0.72       (![X34 : $i, X35 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.49/0.72           | ~ (l1_pre_topc @ X35)
% 0.49/0.72           | ~ (v2_pre_topc @ X35)))),
% 0.49/0.72      inference('split', [status(esa)], ['13'])).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      ((![X32 : $i, X33 : $i]:
% 0.49/0.72          (~ (l1_pre_topc @ X32)
% 0.49/0.72           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.72           | ~ (v3_pre_topc @ X33 @ X32)
% 0.49/0.72           | ((k1_tops_1 @ X32 @ X33) = (X33))))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i]:
% 0.49/0.72         (~ (l1_pre_topc @ X32)
% 0.49/0.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.49/0.72          | ~ (v3_pre_topc @ X33 @ X32)
% 0.49/0.72          | ((k1_tops_1 @ X32 @ X33) = (X33)))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['11', '20'])).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.49/0.72         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.49/0.72         | ~ (l1_pre_topc @ sk_A)))
% 0.49/0.72         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['9', '21'])).
% 0.49/0.72  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('24', plain,
% 0.49/0.72      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.49/0.72         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.72  thf('25', plain,
% 0.49/0.72      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.49/0.72         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.49/0.72             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['8', '24'])).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      (![X38 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72          | ((X38) = (k1_xboole_0))
% 0.49/0.72          | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72          | ~ (r1_tarski @ X38 @ sk_B_1)
% 0.49/0.72          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.49/0.72       (![X38 : $i]:
% 0.49/0.72          (((X38) = (k1_xboole_0))
% 0.49/0.72           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72           | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72           | ~ (r1_tarski @ X38 @ sk_B_1)))),
% 0.49/0.72      inference('split', [status(esa)], ['26'])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(t44_tops_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( l1_pre_topc @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      (![X27 : $i, X28 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.49/0.72          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 0.49/0.72          | ~ (l1_pre_topc @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.49/0.72  thf('30', plain,
% 0.49/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.72        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.72  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('32', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['30', '31'])).
% 0.49/0.72  thf(t28_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i]:
% 0.49/0.72         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.49/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.72  thf('34', plain,
% 0.49/0.72      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.49/0.72         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      (((k3_xboole_0 @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.49/0.72         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 0.49/0.72      inference('demod', [status(thm)], ['34', '35'])).
% 0.49/0.72  thf('37', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(t3_subset, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.72  thf('38', plain,
% 0.49/0.72      (![X14 : $i, X15 : $i]:
% 0.49/0.72         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.72  thf('39', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.72  thf(t108_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.72         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k3_xboole_0 @ X2 @ X4) @ X3))),
% 0.49/0.72      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (r1_tarski @ (k3_xboole_0 @ sk_B_1 @ X0) @ (u1_struct_0 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.72  thf('42', plain,
% 0.49/0.72      (![X14 : $i, X16 : $i]:
% 0.49/0.72         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (m1_subset_1 @ (k3_xboole_0 @ sk_B_1 @ X0) @ 
% 0.49/0.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['41', '42'])).
% 0.49/0.72  thf('44', plain,
% 0.49/0.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['36', '43'])).
% 0.49/0.72  thf('45', plain,
% 0.49/0.72      ((![X38 : $i]:
% 0.49/0.72          (((X38) = (k1_xboole_0))
% 0.49/0.72           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72           | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72           | ~ (r1_tarski @ X38 @ sk_B_1)))
% 0.49/0.72         <= ((![X38 : $i]:
% 0.49/0.72                (((X38) = (k1_xboole_0))
% 0.49/0.72                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72                 | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72                 | ~ (r1_tarski @ X38 @ sk_B_1))))),
% 0.49/0.72      inference('split', [status(esa)], ['26'])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.49/0.72         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.49/0.72         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.49/0.72         <= ((![X38 : $i]:
% 0.49/0.72                (((X38) = (k1_xboole_0))
% 0.49/0.72                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72                 | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72                 | ~ (r1_tarski @ X38 @ sk_B_1))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.72  thf('47', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.49/0.72      inference('demod', [status(thm)], ['30', '31'])).
% 0.49/0.72  thf('48', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(fc9_tops_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.49/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.72       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.49/0.72  thf('49', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i]:
% 0.49/0.72         (~ (l1_pre_topc @ X25)
% 0.49/0.72          | ~ (v2_pre_topc @ X25)
% 0.49/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.49/0.72          | (v3_pre_topc @ (k1_tops_1 @ X25 @ X26) @ X25))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.49/0.72  thf('50', plain,
% 0.49/0.72      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.49/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.72  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('53', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.49/0.72      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.49/0.72  thf('54', plain,
% 0.49/0.72      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.49/0.72         <= ((![X38 : $i]:
% 0.49/0.72                (((X38) = (k1_xboole_0))
% 0.49/0.72                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72                 | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72                 | ~ (r1_tarski @ X38 @ sk_B_1))))),
% 0.49/0.72      inference('demod', [status(thm)], ['46', '47', '53'])).
% 0.49/0.72  thf('55', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(t84_tops_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( l1_pre_topc @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.72           ( ( v2_tops_1 @ B @ A ) <=>
% 0.49/0.72             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.49/0.72  thf('56', plain,
% 0.49/0.72      (![X36 : $i, X37 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.49/0.72          | ((k1_tops_1 @ X37 @ X36) != (k1_xboole_0))
% 0.49/0.72          | (v2_tops_1 @ X36 @ X37)
% 0.49/0.72          | ~ (l1_pre_topc @ X37))),
% 0.49/0.72      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.49/0.72  thf('57', plain,
% 0.49/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.72        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.72  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('59', plain,
% 0.49/0.72      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['57', '58'])).
% 0.49/0.72  thf('60', plain,
% 0.49/0.72      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.49/0.72         <= ((![X38 : $i]:
% 0.49/0.72                (((X38) = (k1_xboole_0))
% 0.49/0.72                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72                 | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72                 | ~ (r1_tarski @ X38 @ sk_B_1))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['54', '59'])).
% 0.49/0.72  thf('61', plain,
% 0.49/0.72      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.49/0.72         <= ((![X38 : $i]:
% 0.49/0.72                (((X38) = (k1_xboole_0))
% 0.49/0.72                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72                 | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72                 | ~ (r1_tarski @ X38 @ sk_B_1))))),
% 0.49/0.72      inference('simplify', [status(thm)], ['60'])).
% 0.49/0.72  thf('62', plain,
% 0.49/0.72      (((r1_tarski @ sk_C @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('63', plain,
% 0.49/0.72      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['62'])).
% 0.49/0.72  thf('64', plain,
% 0.49/0.72      (~
% 0.49/0.72       (![X38 : $i]:
% 0.49/0.72          (((X38) = (k1_xboole_0))
% 0.49/0.72           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72           | ~ (v3_pre_topc @ X38 @ sk_A)
% 0.49/0.72           | ~ (r1_tarski @ X38 @ sk_B_1))) | 
% 0.49/0.72       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['61', '63'])).
% 0.49/0.72  thf('65', plain,
% 0.49/0.72      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('split', [status(esa)], ['7'])).
% 0.49/0.72  thf('66', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['27', '64', '65'])).
% 0.49/0.72  thf('67', plain,
% 0.49/0.72      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.49/0.72       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('split', [status(esa)], ['1'])).
% 0.49/0.72  thf('68', plain,
% 0.49/0.72      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['27', '64', '67'])).
% 0.49/0.72  thf('69', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['25', '66', '68'])).
% 0.49/0.72  thf('70', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.49/0.72           | ~ (r1_tarski @ sk_C @ X0)))
% 0.49/0.72         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '69'])).
% 0.49/0.72  thf('71', plain,
% 0.49/0.72      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['27', '64', '67'])).
% 0.49/0.72  thf('72', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.72          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.49/0.72          | ~ (r1_tarski @ sk_C @ X0))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.49/0.72  thf('73', plain,
% 0.49/0.72      ((~ (r1_tarski @ sk_C @ sk_B_1)
% 0.49/0.72        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['0', '72'])).
% 0.49/0.72  thf('74', plain,
% 0.49/0.72      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.49/0.72      inference('split', [status(esa)], ['62'])).
% 0.49/0.72  thf('75', plain,
% 0.49/0.72      (((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('split', [status(esa)], ['62'])).
% 0.49/0.72  thf('76', plain, (((r1_tarski @ sk_C @ sk_B_1))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['27', '64', '75'])).
% 0.49/0.72  thf('77', plain, ((r1_tarski @ sk_C @ sk_B_1)),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['74', '76'])).
% 0.49/0.72  thf('78', plain,
% 0.49/0.72      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['26'])).
% 0.49/0.72  thf('79', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      (![X36 : $i, X37 : $i]:
% 0.49/0.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.49/0.72          | ~ (v2_tops_1 @ X36 @ X37)
% 0.49/0.72          | ((k1_tops_1 @ X37 @ X36) = (k1_xboole_0))
% 0.49/0.72          | ~ (l1_pre_topc @ X37))),
% 0.49/0.72      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.49/0.72  thf('81', plain,
% 0.49/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.72        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.49/0.72        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['79', '80'])).
% 0.49/0.72  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.49/0.72        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('demod', [status(thm)], ['81', '82'])).
% 0.49/0.72  thf('84', plain,
% 0.49/0.72      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.49/0.72         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['78', '83'])).
% 0.49/0.72  thf('85', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['27', '64'])).
% 0.49/0.72  thf('86', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['84', '85'])).
% 0.49/0.72  thf('87', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.49/0.72      inference('demod', [status(thm)], ['73', '77', '86'])).
% 0.49/0.72  thf('88', plain,
% 0.49/0.72      (![X8 : $i, X9 : $i]:
% 0.49/0.72         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.49/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.72  thf('89', plain, (((k3_xboole_0 @ sk_C @ k1_xboole_0) = (sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['87', '88'])).
% 0.49/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.49/0.72  thf('90', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.49/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.72  thf('91', plain,
% 0.49/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.72         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k3_xboole_0 @ X2 @ X4) @ X3))),
% 0.49/0.72      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.49/0.72  thf('92', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ k1_xboole_0 @ X1) @ X0)),
% 0.49/0.72      inference('sup-', [status(thm)], ['90', '91'])).
% 0.49/0.72  thf(t9_mcart_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.49/0.72          ( ![B:$i]:
% 0.49/0.72            ( ~( ( r2_hidden @ B @ A ) & 
% 0.56/0.72                 ( ![C:$i,D:$i]:
% 0.56/0.72                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.56/0.72                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.56/0.72  thf('93', plain,
% 0.56/0.72      (![X22 : $i]:
% 0.56/0.72         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.56/0.72      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.56/0.72  thf(t7_ordinal1, axiom,
% 0.56/0.72    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.56/0.72  thf('94', plain,
% 0.56/0.72      (![X20 : $i, X21 : $i]:
% 0.56/0.72         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.56/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.56/0.72  thf('95', plain,
% 0.56/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['93', '94'])).
% 0.56/0.72  thf('96', plain,
% 0.56/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.56/0.72      inference('sup-', [status(thm)], ['92', '95'])).
% 0.56/0.72  thf('97', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.56/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.72  thf('98', plain,
% 0.56/0.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.72      inference('sup+', [status(thm)], ['96', '97'])).
% 0.56/0.72  thf('99', plain, (((k1_xboole_0) = (sk_C))),
% 0.56/0.72      inference('demod', [status(thm)], ['89', '98'])).
% 0.56/0.72  thf('100', plain,
% 0.56/0.72      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('101', plain,
% 0.56/0.72      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.56/0.72      inference('split', [status(esa)], ['100'])).
% 0.56/0.72  thf('102', plain,
% 0.56/0.72      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.56/0.72      inference('split', [status(esa)], ['100'])).
% 0.56/0.72  thf('103', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.56/0.72      inference('sat_resolution*', [status(thm)], ['27', '64', '102'])).
% 0.56/0.72  thf('104', plain, (((sk_C) != (k1_xboole_0))),
% 0.56/0.72      inference('simpl_trail', [status(thm)], ['101', '103'])).
% 0.56/0.72  thf('105', plain, ($false),
% 0.56/0.72      inference('simplify_reflect-', [status(thm)], ['99', '104'])).
% 0.56/0.72  
% 0.56/0.72  % SZS output end Refutation
% 0.56/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
