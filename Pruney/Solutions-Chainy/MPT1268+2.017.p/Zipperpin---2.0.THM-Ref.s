%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.riLgKkHn9d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 219 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          : 1486 (3572 expanded)
%              Number of equality atoms :   53 ( 132 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( r1_tarski @ X24 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tops_1 @ X22 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

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

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('19',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('22',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ~ ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) )
    | ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 ) ) ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 ) ) ),
    inference(simpl_trail,[status(thm)],['19','27'])).

thf('29',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
      = sk_C_1 )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ X11 ) @ ( k1_tops_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['15','42'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('45',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('47',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_tops_1 @ X15 @ X14 ) )
      | ( v3_pre_topc @ ( sk_D @ X14 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_tops_1 @ X15 @ X14 ) )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X16 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B )
        | ~ ( v3_pre_topc @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 )
        | ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_tops_1 @ X15 @ X14 ) )
      | ( r1_tarski @ ( sk_D @ X14 @ X16 @ X15 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
          = k1_xboole_0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_tops_1 @ X15 @ X14 ) )
      | ( r2_hidden @ X16 @ ( sk_D @ X14 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_D @ sk_B @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('87',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','88'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('90',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ X22 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ~ ! [X24: $i] :
          ( ( X24 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X24 @ sk_A )
          | ~ ( r1_tarski @ X24 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','48','49','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.riLgKkHn9d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:38:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 317 iterations in 0.121s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(t86_tops_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.56             ( ![C:$i]:
% 0.21/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.56                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56              ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.56                ( ![C:$i]:
% 0.21/0.56                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.56                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['4'])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.56       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X24 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ((X24) = (k1_xboole_0))
% 0.21/0.56          | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56          | ~ (r1_tarski @ X24 @ sk_B)
% 0.21/0.56          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t84_tops_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.56             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X22 : $i, X23 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.56          | ~ (v2_tops_1 @ X22 @ X23)
% 0.21/0.56          | ((k1_tops_1 @ X23 @ X22) = (k1_xboole_0))
% 0.21/0.56          | ~ (l1_pre_topc @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['2'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('split', [status(esa)], ['6'])).
% 0.21/0.56  thf(t55_tops_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( l1_pre_topc @ B ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.56                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.21/0.56                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.21/0.56                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.21/0.56                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X18)
% 0.21/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | ~ (v3_pre_topc @ X19 @ X18)
% 0.21/0.56          | ((k1_tops_1 @ X18 @ X19) = (X19))
% 0.21/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56          | ~ (l1_pre_topc @ X21)
% 0.21/0.56          | ~ (v2_pre_topc @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((![X18 : $i, X19 : $i]:
% 0.21/0.56          (~ (l1_pre_topc @ X18)
% 0.21/0.56           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56           | ~ (v3_pre_topc @ X19 @ X18)
% 0.21/0.56           | ((k1_tops_1 @ X18 @ X19) = (X19))))
% 0.21/0.56         <= ((![X18 : $i, X19 : $i]:
% 0.21/0.56                (~ (l1_pre_topc @ X18)
% 0.21/0.56                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56                 | ~ (v3_pre_topc @ X19 @ X18)
% 0.21/0.56                 | ((k1_tops_1 @ X18 @ X19) = (X19)))))),
% 0.21/0.56      inference('split', [status(esa)], ['18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((![X20 : $i, X21 : $i]:
% 0.21/0.56          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56           | ~ (l1_pre_topc @ X21)
% 0.21/0.56           | ~ (v2_pre_topc @ X21)))
% 0.21/0.56         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.56                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56                 | ~ (l1_pre_topc @ X21)
% 0.21/0.56                 | ~ (v2_pre_topc @ X21))))),
% 0.21/0.56      inference('split', [status(esa)], ['18'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.56         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.56                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56                 | ~ (l1_pre_topc @ X21)
% 0.21/0.56                 | ~ (v2_pre_topc @ X21))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (~
% 0.21/0.56       (![X20 : $i, X21 : $i]:
% 0.21/0.56          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56           | ~ (l1_pre_topc @ X21)
% 0.21/0.56           | ~ (v2_pre_topc @ X21)))),
% 0.21/0.56      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((![X18 : $i, X19 : $i]:
% 0.21/0.56          (~ (l1_pre_topc @ X18)
% 0.21/0.56           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56           | ~ (v3_pre_topc @ X19 @ X18)
% 0.21/0.56           | ((k1_tops_1 @ X18 @ X19) = (X19)))) | 
% 0.21/0.56       (![X20 : $i, X21 : $i]:
% 0.21/0.56          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.56           | ~ (l1_pre_topc @ X21)
% 0.21/0.56           | ~ (v2_pre_topc @ X21)))),
% 0.21/0.56      inference('split', [status(esa)], ['18'])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      ((![X18 : $i, X19 : $i]:
% 0.21/0.56          (~ (l1_pre_topc @ X18)
% 0.21/0.56           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56           | ~ (v3_pre_topc @ X19 @ X18)
% 0.21/0.56           | ((k1_tops_1 @ X18 @ X19) = (X19))))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X18)
% 0.21/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | ~ (v3_pre_topc @ X19 @ X18)
% 0.21/0.56          | ((k1_tops_1 @ X18 @ X19) = (X19)))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['19', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))
% 0.21/0.56         | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.21/0.56         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.56         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['17', '28'])).
% 0.21/0.56  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))
% 0.21/0.56         | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 0.21/0.56         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1)))
% 0.21/0.56         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.21/0.56             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('split', [status(esa)], ['6'])).
% 0.21/0.56  thf(t48_tops_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ( r1_tarski @ B @ C ) =>
% 0.21/0.56                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.56          | ~ (r1_tarski @ X11 @ X13)
% 0.21/0.56          | (r1_tarski @ (k1_tops_1 @ X12 @ X11) @ (k1_tops_1 @ X12 @ X13))
% 0.21/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.56          | ~ (l1_pre_topc @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (l1_pre_topc @ sk_A)
% 0.21/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.56           | ~ (r1_tarski @ sk_C_1 @ X0)))
% 0.21/0.56         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.56           | ~ (r1_tarski @ sk_C_1 @ X0)))
% 0.21/0.56         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (((~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.21/0.56         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.56         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.56         <= (((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.21/0.56             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.56         <= (((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.21/0.56             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.21/0.56             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['32', '41'])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 0.21/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.21/0.56             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.21/0.56             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.21/0.56             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['15', '42'])).
% 0.21/0.56  thf(t3_xboole_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      ((((sk_C_1) = (k1_xboole_0)))
% 0.21/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.21/0.56             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.21/0.56             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.21/0.56             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['4'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      ((((sk_C_1) != (sk_C_1)))
% 0.21/0.56         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 0.21/0.56             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.21/0.56             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.21/0.56             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.21/0.56             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.21/0.56       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.56       ~ ((r1_tarski @ sk_C_1 @ sk_B)) | (((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((![X24 : $i]:
% 0.21/0.56          (((X24) = (k1_xboole_0))
% 0.21/0.56           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.21/0.56       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['8'])).
% 0.21/0.56  thf(d3_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t54_tops_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i,C:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.21/0.56             ( ?[D:$i]:
% 0.21/0.56               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.21/0.56                 ( v3_pre_topc @ D @ A ) & 
% 0.21/0.56                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (r2_hidden @ X16 @ (k1_tops_1 @ X15 @ X14))
% 0.21/0.56          | (v3_pre_topc @ (sk_D @ X14 @ X16 @ X15) @ X15)
% 0.21/0.56          | ~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | (v3_pre_topc @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v3_pre_topc @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.56          | (v3_pre_topc @ 
% 0.21/0.56             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.56             sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['50', '56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (r2_hidden @ X16 @ (k1_tops_1 @ X15 @ X14))
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ X14 @ X16 @ X15) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.56          | (m1_subset_1 @ 
% 0.21/0.56             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['58', '64'])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      ((![X24 : $i]:
% 0.21/0.56          (((X24) = (k1_xboole_0))
% 0.21/0.56           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56           | ~ (r1_tarski @ X24 @ sk_B)))
% 0.21/0.56         <= ((![X24 : $i]:
% 0.21/0.56                (((X24) = (k1_xboole_0))
% 0.21/0.56                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.56      inference('split', [status(esa)], ['8'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.56           | ~ (r1_tarski @ 
% 0.21/0.56                (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.56                sk_B)
% 0.21/0.56           | ~ (v3_pre_topc @ 
% 0.21/0.56                (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.56                sk_A)
% 0.21/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.21/0.56               = (k1_xboole_0))))
% 0.21/0.56         <= ((![X24 : $i]:
% 0.21/0.56                (((X24) = (k1_xboole_0))
% 0.21/0.56                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.21/0.56               = (k1_xboole_0))
% 0.21/0.56           | ~ (r1_tarski @ 
% 0.21/0.56                (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.56                sk_B)
% 0.21/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.21/0.56         <= ((![X24 : $i]:
% 0.21/0.56                (((X24) = (k1_xboole_0))
% 0.21/0.56                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['57', '67'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (r1_tarski @ 
% 0.21/0.56              (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.56              sk_B)
% 0.21/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.21/0.56               = (k1_xboole_0))
% 0.21/0.56           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.21/0.56         <= ((![X24 : $i]:
% 0.21/0.56                (((X24) = (k1_xboole_0))
% 0.21/0.56                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (r2_hidden @ X16 @ (k1_tops_1 @ X15 @ X14))
% 0.21/0.56          | (r1_tarski @ (sk_D @ X14 @ X16 @ X15) @ X14)
% 0.21/0.56          | ~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | (r1_tarski @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.56  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.56          | (r1_tarski @ 
% 0.21/0.56             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.56             sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['70', '76'])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.56           | ((sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.21/0.56               = (k1_xboole_0))))
% 0.21/0.56         <= ((![X24 : $i]:
% 0.21/0.56                (((X24) = (k1_xboole_0))
% 0.21/0.56                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.56                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.56      inference('clc', [status(thm)], ['69', '77'])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (r2_hidden @ X16 @ (k1_tops_1 @ X15 @ X14))
% 0.21/0.56          | (r2_hidden @ X16 @ (sk_D @ X14 @ X16 @ X15))
% 0.21/0.56          | ~ (l1_pre_topc @ X15)
% 0.21/0.56          | ~ (v2_pre_topc @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_pre_topc @ sk_A)
% 0.21/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | (r2_hidden @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.56  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ X0 @ (sk_D @ sk_B @ X0 @ sk_A))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.57          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.21/0.57             (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['79', '85'])).
% 0.21/0.57  thf(t7_ordinal1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.57          | ~ (r1_tarski @ 
% 0.21/0.57               (sk_D @ sk_B @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 0.21/0.57               (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.57           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.57           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.21/0.57         <= ((![X24 : $i]:
% 0.21/0.57                (((X24) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['78', '88'])).
% 0.21/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.57  thf('90', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.57           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)))
% 0.21/0.57         <= ((![X24 : $i]:
% 0.21/0.57                (((X24) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      ((![X0 : $i]: (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.57         <= ((![X24 : $i]:
% 0.21/0.57                (((X24) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['91'])).
% 0.21/0.57  thf('93', plain,
% 0.21/0.57      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.57  thf('94', plain,
% 0.21/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= ((![X24 : $i]:
% 0.21/0.57                (((X24) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | ((k1_tops_1 @ X23 @ X22) != (k1_xboole_0))
% 0.21/0.57          | (v2_tops_1 @ X22 @ X23)
% 0.21/0.57          | ~ (l1_pre_topc @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.57  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['97', '98'])).
% 0.21/0.57  thf('100', plain,
% 0.21/0.57      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.21/0.57         <= ((![X24 : $i]:
% 0.21/0.57                (((X24) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['94', '99'])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      (((v2_tops_1 @ sk_B @ sk_A))
% 0.21/0.57         <= ((![X24 : $i]:
% 0.21/0.57                (((X24) = (k1_xboole_0))
% 0.21/0.57                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.57                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['100'])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      (~
% 0.21/0.57       (![X24 : $i]:
% 0.21/0.57          (((X24) = (k1_xboole_0))
% 0.21/0.57           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.21/0.57           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.21/0.57       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.57  thf('104', plain, ($false),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['1', '3', '5', '7', '48', '49', '103'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
