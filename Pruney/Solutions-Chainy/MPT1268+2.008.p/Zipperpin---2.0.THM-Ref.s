%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SiakVseXhn

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:16 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 169 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  911 (2382 expanded)
%              Number of equality atoms :   44 ( 100 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( r1_tarski @ X27 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,
    ( ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('22',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ~ ! [X27: $i] :
          ( ( X27 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X27 @ sk_A )
          | ~ ( r1_tarski @ X27 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('38',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['42'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('64',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('72',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','39','41','43','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SiakVseXhn
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 310 iterations in 0.116s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.42/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(t86_tops_1, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ( v2_tops_1 @ B @ A ) <=>
% 0.42/0.61             ( ![C:$i]:
% 0.42/0.61               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.42/0.61                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61          ( ![B:$i]:
% 0.42/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61              ( ( v2_tops_1 @ B @ A ) <=>
% 0.42/0.61                ( ![C:$i]:
% 0.42/0.61                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.42/0.61                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X27 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | ((X27) = (k1_xboole_0))
% 0.42/0.61          | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X27 @ sk_B)
% 0.42/0.61          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      ((![X27 : $i]:
% 0.42/0.61          (((X27) = (k1_xboole_0))
% 0.42/0.61           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61           | ~ (r1_tarski @ X27 @ sk_B))) | 
% 0.42/0.61       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t44_tops_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_pre_topc @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.61          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ X20)
% 0.42/0.61          | ~ (l1_pre_topc @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('6', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.42/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.61  thf(t28_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.42/0.61         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k9_subset_1 @ X10 @ X11 @ X12) @ (k1_zfmisc_1 @ X10))
% 0.42/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.42/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['11', '14'])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.42/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['8', '15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      ((![X27 : $i]:
% 0.42/0.61          (((X27) = (k1_xboole_0))
% 0.42/0.61           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61           | ~ (r1_tarski @ X27 @ sk_B)))
% 0.42/0.61         <= ((![X27 : $i]:
% 0.42/0.61                (((X27) = (k1_xboole_0))
% 0.42/0.61                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61                 | ~ (r1_tarski @ X27 @ sk_B))))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.42/0.61         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.42/0.61         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.42/0.61         <= ((![X27 : $i]:
% 0.42/0.61                (((X27) = (k1_xboole_0))
% 0.42/0.61                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61                 | ~ (r1_tarski @ X27 @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.61  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.42/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(fc9_tops_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.42/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.61       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i]:
% 0.42/0.61         (~ (l1_pre_topc @ X18)
% 0.42/0.61          | ~ (v2_pre_topc @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.61          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.42/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('25', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.42/0.61         <= ((![X27 : $i]:
% 0.42/0.61                (((X27) = (k1_xboole_0))
% 0.42/0.61                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61                 | ~ (r1_tarski @ X27 @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['18', '19', '25'])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t84_tops_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_pre_topc @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ( v2_tops_1 @ B @ A ) <=>
% 0.42/0.61             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X25 : $i, X26 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.42/0.61          | ((k1_tops_1 @ X26 @ X25) != (k1_xboole_0))
% 0.42/0.61          | (v2_tops_1 @ X25 @ X26)
% 0.42/0.61          | ~ (l1_pre_topc @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.61        | (v2_tops_1 @ sk_B @ sk_A)
% 0.42/0.61        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.61  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (((v2_tops_1 @ sk_B @ sk_A)
% 0.42/0.61        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.42/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.42/0.61         <= ((![X27 : $i]:
% 0.42/0.61                (((X27) = (k1_xboole_0))
% 0.42/0.61                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61                 | ~ (r1_tarski @ X27 @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['26', '31'])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (((v2_tops_1 @ sk_B @ sk_A))
% 0.42/0.61         <= ((![X27 : $i]:
% 0.42/0.61                (((X27) = (k1_xboole_0))
% 0.42/0.61                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61                 | ~ (r1_tarski @ X27 @ sk_B))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['32'])).
% 0.42/0.61  thf('34', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['34'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (~
% 0.42/0.61       (![X27 : $i]:
% 0.42/0.61          (((X27) = (k1_xboole_0))
% 0.42/0.61           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.42/0.61           | ~ (r1_tarski @ X27 @ sk_B))) | 
% 0.42/0.61       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '35'])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['34'])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['38'])).
% 0.42/0.61  thf('40', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['40'])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.42/0.61       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['42'])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X25 : $i, X26 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.42/0.61          | ~ (v2_tops_1 @ X25 @ X26)
% 0.42/0.61          | ((k1_tops_1 @ X26 @ X25) = (k1_xboole_0))
% 0.42/0.61          | ~ (l1_pre_topc @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.61        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.61        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.42/0.61        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.42/0.61         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['44', '49'])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.42/0.61      inference('split', [status(esa)], ['34'])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['38'])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.42/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('split', [status(esa)], ['42'])).
% 0.42/0.61  thf(t56_tops_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_pre_topc @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.42/0.61                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.61          | ~ (v3_pre_topc @ X22 @ X23)
% 0.42/0.61          | ~ (r1_tarski @ X22 @ X24)
% 0.42/0.61          | (r1_tarski @ X22 @ (k1_tops_1 @ X23 @ X24))
% 0.42/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.61          | ~ (l1_pre_topc @ X23))),
% 0.42/0.61      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      ((![X0 : $i]:
% 0.42/0.61          (~ (l1_pre_topc @ sk_A)
% 0.42/0.61           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.42/0.61           | ~ (r1_tarski @ sk_C @ X0)
% 0.42/0.61           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.42/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.42/0.61  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      ((![X0 : $i]:
% 0.42/0.61          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.42/0.61           | ~ (r1_tarski @ sk_C @ X0)
% 0.42/0.61           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.42/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      ((![X0 : $i]:
% 0.42/0.61          (~ (r1_tarski @ sk_C @ X0)
% 0.42/0.61           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.42/0.61           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.42/0.61         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.42/0.61             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '58'])).
% 0.42/0.61  thf('60', plain,
% 0.42/0.61      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.42/0.61         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.42/0.61         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.42/0.61             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['52', '59'])).
% 0.42/0.61  thf('61', plain,
% 0.42/0.61      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.42/0.61         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.42/0.61             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.42/0.61             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['51', '60'])).
% 0.42/0.61  thf('62', plain,
% 0.42/0.61      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.42/0.61         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.42/0.61             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.42/0.61             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.42/0.61             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['50', '61'])).
% 0.42/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.42/0.61  thf('63', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.61  thf(t1_boole, axiom,
% 0.42/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.61  thf('64', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.42/0.61  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['63', '64'])).
% 0.42/0.61  thf(t7_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('66', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.42/0.61  thf('67', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.42/0.61  thf(d10_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.61  thf('68', plain,
% 0.42/0.61      (![X2 : $i, X4 : $i]:
% 0.42/0.61         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.61  thf('69', plain,
% 0.42/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.61  thf('70', plain,
% 0.42/0.61      ((((sk_C) = (k1_xboole_0)))
% 0.42/0.61         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.42/0.61             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.42/0.61             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.42/0.61             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '69'])).
% 0.42/0.61  thf('71', plain,
% 0.42/0.61      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.42/0.61      inference('split', [status(esa)], ['40'])).
% 0.42/0.61  thf('72', plain,
% 0.42/0.61      ((((sk_C) != (sk_C)))
% 0.42/0.61         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.42/0.61             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.42/0.61             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.42/0.61             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.42/0.61             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.61  thf('73', plain,
% 0.42/0.61      (~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.42/0.61       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.42/0.61       ~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.42/0.61       (((sk_C) = (k1_xboole_0)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['72'])).
% 0.42/0.61  thf('74', plain, ($false),
% 0.42/0.61      inference('sat_resolution*', [status(thm)],
% 0.42/0.61                ['1', '36', '37', '39', '41', '43', '73'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
