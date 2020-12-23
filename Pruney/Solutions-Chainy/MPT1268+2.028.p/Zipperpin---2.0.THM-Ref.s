%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oAJghsHxEP

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 799 expanded)
%              Number of leaves         :   25 ( 211 expanded)
%              Depth                    :   21
%              Number of atoms          : 1288 (12877 expanded)
%              Number of equality atoms :   64 ( 546 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ ( k1_tops_1 @ X20 @ X19 ) @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('11',plain,
    ( ! [X22: $i,X23: $i] :
        ( ~ ( l1_pre_topc @ X22 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( v3_pre_topc @ X23 @ X22 )
        | ( ( k1_tops_1 @ X22 @ X23 )
          = X23 ) )
   <= ! [X22: $i,X23: $i] :
        ( ~ ( l1_pre_topc @ X22 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( v3_pre_topc @ X23 @ X22 )
        | ( ( k1_tops_1 @ X22 @ X23 )
          = X23 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('14',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( l1_pre_topc @ X25 )
        | ~ ( v2_pre_topc @ X25 ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( l1_pre_topc @ X25 )
        | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( l1_pre_topc @ X25 )
        | ~ ( v2_pre_topc @ X25 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ! [X24: $i,X25: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( l1_pre_topc @ X25 )
        | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ! [X22: $i,X23: $i] :
        ( ~ ( l1_pre_topc @ X22 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( v3_pre_topc @ X23 @ X22 )
        | ( ( k1_tops_1 @ X22 @ X23 )
          = X23 ) )
    | ! [X24: $i,X25: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
        | ~ ( l1_pre_topc @ X25 )
        | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X23 )
        = X23 ) ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X23 )
        = X23 ) ) ),
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

thf('26',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X28 @ sk_A )
      | ~ ( r1_tarski @ X28 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('50',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('63',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ! [X28: $i] :
          ( ( X28 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X28 @ sk_A )
          | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('65',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('67',plain,
    ( ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('68',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_B )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ! [X28: $i] :
          ( ( X28 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X28 @ sk_A )
          | ~ ( r1_tarski @ X28 @ sk_B ) )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( ! [X28: $i] :
          ( ( X28 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X28 @ sk_A )
          | ~ ( r1_tarski @ X28 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ! [X28: $i] :
          ( ( X28 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X28 @ sk_A )
          | ~ ( r1_tarski @ X28 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('72',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ! [X28: $i] :
          ( ( X28 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X28 @ sk_A )
          | ~ ( r1_tarski @ X28 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ! [X28: $i] :
          ( ( X28 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X28 @ sk_A )
          | ~ ( r1_tarski @ X28 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X28: $i] :
        ( ( X28 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X28 @ sk_A )
        | ~ ( r1_tarski @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('76',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','29','30','63','73','74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','75','29','63','73','74','30'])).

thf('78',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['25','76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','75','29','63','73','74','30'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('84',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['75','29','30','63','73','74','27'])).

thf('85',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tops_1 @ X26 @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','75','29','30','63','73','74'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['82','85','94'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
    | ( k1_xboole_0 = sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('98',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('101',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['98','102'])).

thf('104',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['97','103'])).

thf('105',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('106',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['27','75','30','63','73','74','29'])).

thf('107',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oAJghsHxEP
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:39:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 343 iterations in 0.126s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.59  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.22/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.59  thf(t86_tops_1, conjecture,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.59             ( ![C:$i]:
% 0.22/0.59               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.22/0.59                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.59    (~( ![A:$i]:
% 0.22/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59          ( ![B:$i]:
% 0.22/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59              ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.59                ( ![C:$i]:
% 0.22/0.59                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.22/0.59                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.22/0.59  thf('0', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('2', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['1'])).
% 0.22/0.59  thf(t48_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ![C:$i]:
% 0.22/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59               ( ( r1_tarski @ B @ C ) =>
% 0.22/0.59                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.59          | ~ (r1_tarski @ X19 @ X21)
% 0.22/0.59          | (r1_tarski @ (k1_tops_1 @ X20 @ X19) @ (k1_tops_1 @ X20 @ X21))
% 0.22/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.59          | ~ (l1_pre_topc @ X20))),
% 0.22/0.59      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.22/0.59  thf('4', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (l1_pre_topc @ sk_A)
% 0.22/0.59           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.59           | ~ (r1_tarski @ sk_C @ X0)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.59  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.59           | ~ (r1_tarski @ sk_C @ X0)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.59  thf('7', plain,
% 0.22/0.59      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('8', plain,
% 0.22/0.59      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['7'])).
% 0.22/0.59  thf('9', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['1'])).
% 0.22/0.59  thf(t55_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( l1_pre_topc @ B ) =>
% 0.22/0.59           ( ![C:$i]:
% 0.22/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59               ( ![D:$i]:
% 0.22/0.59                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.59                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.22/0.59                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.22/0.59                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.22/0.59                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.59  thf('10', plain,
% 0.22/0.59      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.59         (~ (l1_pre_topc @ X22)
% 0.22/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59          | ~ (v3_pre_topc @ X23 @ X22)
% 0.22/0.59          | ((k1_tops_1 @ X22 @ X23) = (X23))
% 0.22/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59          | ~ (l1_pre_topc @ X25)
% 0.22/0.59          | ~ (v2_pre_topc @ X25))),
% 0.22/0.59      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.22/0.59  thf('11', plain,
% 0.22/0.59      ((![X22 : $i, X23 : $i]:
% 0.22/0.59          (~ (l1_pre_topc @ X22)
% 0.22/0.59           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59           | ~ (v3_pre_topc @ X23 @ X22)
% 0.22/0.59           | ((k1_tops_1 @ X22 @ X23) = (X23))))
% 0.22/0.59         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.59                (~ (l1_pre_topc @ X22)
% 0.22/0.59                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X23 @ X22)
% 0.22/0.59                 | ((k1_tops_1 @ X22 @ X23) = (X23)))))),
% 0.22/0.59      inference('split', [status(esa)], ['10'])).
% 0.22/0.59  thf('12', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('13', plain,
% 0.22/0.59      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.59         (~ (l1_pre_topc @ X22)
% 0.22/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59          | ~ (v3_pre_topc @ X23 @ X22)
% 0.22/0.59          | ((k1_tops_1 @ X22 @ X23) = (X23))
% 0.22/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59          | ~ (l1_pre_topc @ X25)
% 0.22/0.59          | ~ (v2_pre_topc @ X25))),
% 0.22/0.59      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.22/0.59  thf('14', plain,
% 0.22/0.59      ((![X24 : $i, X25 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59           | ~ (l1_pre_topc @ X25)
% 0.22/0.59           | ~ (v2_pre_topc @ X25)))
% 0.22/0.59         <= ((![X24 : $i, X25 : $i]:
% 0.22/0.59                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59                 | ~ (l1_pre_topc @ X25)
% 0.22/0.59                 | ~ (v2_pre_topc @ X25))))),
% 0.22/0.59      inference('split', [status(esa)], ['13'])).
% 0.22/0.59  thf('15', plain,
% 0.22/0.59      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.22/0.59         <= ((![X24 : $i, X25 : $i]:
% 0.22/0.59                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59                 | ~ (l1_pre_topc @ X25)
% 0.22/0.59                 | ~ (v2_pre_topc @ X25))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.59  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('18', plain,
% 0.22/0.59      (~
% 0.22/0.59       (![X24 : $i, X25 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59           | ~ (l1_pre_topc @ X25)
% 0.22/0.59           | ~ (v2_pre_topc @ X25)))),
% 0.22/0.59      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.59  thf('19', plain,
% 0.22/0.59      ((![X22 : $i, X23 : $i]:
% 0.22/0.59          (~ (l1_pre_topc @ X22)
% 0.22/0.59           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59           | ~ (v3_pre_topc @ X23 @ X22)
% 0.22/0.59           | ((k1_tops_1 @ X22 @ X23) = (X23)))) | 
% 0.22/0.59       (![X24 : $i, X25 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.22/0.59           | ~ (l1_pre_topc @ X25)
% 0.22/0.59           | ~ (v2_pre_topc @ X25)))),
% 0.22/0.59      inference('split', [status(esa)], ['13'])).
% 0.22/0.59  thf('20', plain,
% 0.22/0.59      ((![X22 : $i, X23 : $i]:
% 0.22/0.59          (~ (l1_pre_topc @ X22)
% 0.22/0.59           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59           | ~ (v3_pre_topc @ X23 @ X22)
% 0.22/0.59           | ((k1_tops_1 @ X22 @ X23) = (X23))))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      (![X22 : $i, X23 : $i]:
% 0.22/0.59         (~ (l1_pre_topc @ X22)
% 0.22/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59          | ~ (v3_pre_topc @ X23 @ X22)
% 0.22/0.59          | ((k1_tops_1 @ X22 @ X23) = (X23)))),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['11', '20'])).
% 0.22/0.59  thf('22', plain,
% 0.22/0.59      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.22/0.59         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.22/0.59         | ~ (l1_pre_topc @ sk_A)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['9', '21'])).
% 0.22/0.59  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('24', plain,
% 0.22/0.59      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.59  thf('25', plain,
% 0.22/0.59      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.22/0.59         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['8', '24'])).
% 0.22/0.59  thf('26', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('split', [status(esa)], ['26'])).
% 0.22/0.59  thf('28', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('29', plain,
% 0.22/0.59      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('split', [status(esa)], ['28'])).
% 0.22/0.59  thf('30', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.22/0.59       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('split', [status(esa)], ['1'])).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t3_subset, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.59  thf('32', plain,
% 0.22/0.59      (![X12 : $i, X13 : $i]:
% 0.22/0.59         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.59  thf('33', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.59  thf('34', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t44_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.59  thf('35', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.59          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ X17)
% 0.22/0.59          | ~ (l1_pre_topc @ X18))),
% 0.22/0.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.59  thf('36', plain,
% 0.22/0.59      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.59  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('38', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.59  thf(t1_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.59       ( r1_tarski @ A @ C ) ))).
% 0.22/0.59  thf('39', plain,
% 0.22/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.59         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.59          | ~ (r1_tarski @ X7 @ X8)
% 0.22/0.59          | (r1_tarski @ X6 @ X8))),
% 0.22/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.59  thf('40', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.22/0.59          | ~ (r1_tarski @ sk_B @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.59  thf('41', plain,
% 0.22/0.59      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['33', '40'])).
% 0.22/0.59  thf('42', plain,
% 0.22/0.59      (![X12 : $i, X14 : $i]:
% 0.22/0.59         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.59  thf('43', plain,
% 0.22/0.59      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.22/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.59  thf('44', plain,
% 0.22/0.59      (![X28 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59          | ((X28) = (k1_xboole_0))
% 0.22/0.59          | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59          | ~ (r1_tarski @ X28 @ sk_B)
% 0.22/0.59          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('45', plain,
% 0.22/0.59      ((![X28 : $i]:
% 0.22/0.59          (((X28) = (k1_xboole_0))
% 0.22/0.59           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X28 @ sk_B)))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))))),
% 0.22/0.59      inference('split', [status(esa)], ['44'])).
% 0.22/0.59  thf('46', plain,
% 0.22/0.59      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.22/0.59         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.59         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['43', '45'])).
% 0.22/0.59  thf('47', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.59  thf('48', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(fc9_tops_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.22/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.59       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.22/0.59  thf('49', plain,
% 0.22/0.59      (![X15 : $i, X16 : $i]:
% 0.22/0.59         (~ (l1_pre_topc @ X15)
% 0.22/0.59          | ~ (v2_pre_topc @ X15)
% 0.22/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.59          | (v3_pre_topc @ (k1_tops_1 @ X15 @ X16) @ X15))),
% 0.22/0.59      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.22/0.59  thf('50', plain,
% 0.22/0.59      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.59  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('53', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.59      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.59  thf('54', plain,
% 0.22/0.59      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))))),
% 0.22/0.59      inference('demod', [status(thm)], ['46', '47', '53'])).
% 0.22/0.59  thf('55', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t84_tops_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.59             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.59  thf('56', plain,
% 0.22/0.59      (![X26 : $i, X27 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.59          | ((k1_tops_1 @ X27 @ X26) != (k1_xboole_0))
% 0.22/0.59          | (v2_tops_1 @ X26 @ X27)
% 0.22/0.59          | ~ (l1_pre_topc @ X27))),
% 0.22/0.59      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.59  thf('57', plain,
% 0.22/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | (v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.59        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.59  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('59', plain,
% 0.22/0.59      (((v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.59        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.59      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.59  thf('60', plain,
% 0.22/0.59      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['54', '59'])).
% 0.22/0.59  thf('61', plain,
% 0.22/0.59      (((v2_tops_1 @ sk_B @ sk_A))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))))),
% 0.22/0.59      inference('simplify', [status(thm)], ['60'])).
% 0.22/0.59  thf('62', plain,
% 0.22/0.59      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['26'])).
% 0.22/0.59  thf('63', plain,
% 0.22/0.59      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.22/0.59       ~
% 0.22/0.59       (![X28 : $i]:
% 0.22/0.59          (((X28) = (k1_xboole_0))
% 0.22/0.59           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X28 @ sk_B)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.59  thf('64', plain,
% 0.22/0.59      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['7'])).
% 0.22/0.59  thf('65', plain,
% 0.22/0.59      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.22/0.59      inference('split', [status(esa)], ['26'])).
% 0.22/0.59  thf('66', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('split', [status(esa)], ['1'])).
% 0.22/0.59  thf('67', plain,
% 0.22/0.59      ((![X28 : $i]:
% 0.22/0.59          (((X28) = (k1_xboole_0))
% 0.22/0.59           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X28 @ sk_B)))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))))),
% 0.22/0.59      inference('split', [status(esa)], ['44'])).
% 0.22/0.59  thf('68', plain,
% 0.22/0.59      (((~ (r1_tarski @ sk_C @ sk_B)
% 0.22/0.59         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.22/0.59         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))) & 
% 0.22/0.59             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.59  thf('69', plain,
% 0.22/0.59      (((((sk_C) = (k1_xboole_0)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))) & 
% 0.22/0.59             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['65', '68'])).
% 0.22/0.59  thf('70', plain,
% 0.22/0.59      ((((sk_C) = (k1_xboole_0)))
% 0.22/0.59         <= ((![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))) & 
% 0.22/0.59             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.22/0.59             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['64', '69'])).
% 0.22/0.59  thf('71', plain,
% 0.22/0.59      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.22/0.59      inference('split', [status(esa)], ['28'])).
% 0.22/0.59  thf('72', plain,
% 0.22/0.59      ((((sk_C) != (sk_C)))
% 0.22/0.59         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.22/0.59             (![X28 : $i]:
% 0.22/0.59                (((X28) = (k1_xboole_0))
% 0.22/0.59                 | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59                 | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59                 | ~ (r1_tarski @ X28 @ sk_B))) & 
% 0.22/0.59             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.22/0.59             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.22/0.59             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.59  thf('73', plain,
% 0.22/0.59      (~
% 0.22/0.59       (![X28 : $i]:
% 0.22/0.59          (((X28) = (k1_xboole_0))
% 0.22/0.59           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X28 @ sk_B))) | 
% 0.22/0.59       (((sk_C) = (k1_xboole_0))) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.22/0.59       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.22/0.59       ~ ((r1_tarski @ sk_C @ sk_B))),
% 0.22/0.59      inference('simplify', [status(thm)], ['72'])).
% 0.22/0.59  thf('74', plain,
% 0.22/0.59      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.22/0.59       (![X28 : $i]:
% 0.22/0.59          (((X28) = (k1_xboole_0))
% 0.22/0.59           | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | ~ (v3_pre_topc @ X28 @ sk_A)
% 0.22/0.59           | ~ (r1_tarski @ X28 @ sk_B)))),
% 0.22/0.59      inference('split', [status(esa)], ['44'])).
% 0.22/0.59  thf('75', plain,
% 0.22/0.59      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('split', [status(esa)], ['7'])).
% 0.22/0.59  thf('76', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)],
% 0.22/0.59                ['27', '29', '30', '63', '73', '74', '75'])).
% 0.22/0.59  thf('77', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)],
% 0.22/0.59                ['27', '75', '29', '63', '73', '74', '30'])).
% 0.22/0.59  thf('78', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['25', '76', '77'])).
% 0.22/0.59  thf('79', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.59           | ~ (r1_tarski @ sk_C @ X0)))
% 0.22/0.59         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.59      inference('demod', [status(thm)], ['6', '78'])).
% 0.22/0.59  thf('80', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)],
% 0.22/0.59                ['27', '75', '29', '63', '73', '74', '30'])).
% 0.22/0.59  thf('81', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.59          | ~ (r1_tarski @ sk_C @ X0))),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.22/0.59  thf('82', plain,
% 0.22/0.59      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.22/0.59        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['0', '81'])).
% 0.22/0.59  thf('83', plain,
% 0.22/0.59      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.22/0.59      inference('split', [status(esa)], ['26'])).
% 0.22/0.59  thf('84', plain, (((r1_tarski @ sk_C @ sk_B))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)],
% 0.22/0.59                ['75', '29', '30', '63', '73', '74', '27'])).
% 0.22/0.59  thf('85', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.22/0.59  thf('86', plain,
% 0.22/0.59      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['44'])).
% 0.22/0.59  thf('87', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('88', plain,
% 0.22/0.59      (![X26 : $i, X27 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.59          | ~ (v2_tops_1 @ X26 @ X27)
% 0.22/0.59          | ((k1_tops_1 @ X27 @ X26) = (k1_xboole_0))
% 0.22/0.59          | ~ (l1_pre_topc @ X27))),
% 0.22/0.59      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.59  thf('89', plain,
% 0.22/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.59        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.59  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('91', plain,
% 0.22/0.59      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.59        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('92', plain,
% 0.22/0.59      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.59         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['86', '91'])).
% 0.22/0.59  thf('93', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)],
% 0.22/0.59                ['27', '75', '29', '30', '63', '73', '74'])).
% 0.22/0.59  thf('94', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.22/0.59  thf('95', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.22/0.59      inference('demod', [status(thm)], ['82', '85', '94'])).
% 0.22/0.59  thf(d10_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.59  thf('96', plain,
% 0.22/0.59      (![X0 : $i, X2 : $i]:
% 0.22/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.59  thf('97', plain,
% 0.22/0.59      ((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['95', '96'])).
% 0.22/0.59  thf(t2_boole, axiom,
% 0.22/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.59  thf('98', plain,
% 0.22/0.59      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.59  thf('99', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.59  thf('100', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.59      inference('simplify', [status(thm)], ['99'])).
% 0.22/0.59  thf(t108_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.22/0.59  thf('101', plain,
% 0.22/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.59         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 0.22/0.59      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.22/0.59  thf('102', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.59      inference('sup-', [status(thm)], ['100', '101'])).
% 0.22/0.59  thf('103', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.59      inference('sup+', [status(thm)], ['98', '102'])).
% 0.22/0.59  thf('104', plain, (((k1_xboole_0) = (sk_C))),
% 0.22/0.59      inference('demod', [status(thm)], ['97', '103'])).
% 0.22/0.59  thf('105', plain,
% 0.22/0.59      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.22/0.59      inference('split', [status(esa)], ['28'])).
% 0.22/0.59  thf('106', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)],
% 0.22/0.59                ['27', '75', '30', '63', '73', '74', '29'])).
% 0.22/0.59  thf('107', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.22/0.59  thf('108', plain, ($false),
% 0.22/0.59      inference('simplify_reflect-', [status(thm)], ['104', '107'])).
% 0.22/0.59  
% 0.22/0.59  % SZS output end Refutation
% 0.22/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
