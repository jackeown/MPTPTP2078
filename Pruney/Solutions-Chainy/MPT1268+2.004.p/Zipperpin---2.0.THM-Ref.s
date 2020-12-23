%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L5DG3HlChc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 194 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  979 (2582 expanded)
%              Number of equality atoms :   51 ( 124 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( r1_tarski @ X22 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B ) )
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,
    ( ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('30',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X21 @ X20 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X22: $i] :
        ( ( X22 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X22 @ sk_A )
        | ~ ( r1_tarski @ X22 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ~ ! [X22: $i] :
          ( ( X22 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X22 @ sk_A )
          | ~ ( r1_tarski @ X22 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tops_1 @ X20 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X20 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['50'])).

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

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,
    ( ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
      = sk_C )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('74',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('80',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','47','49','51','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L5DG3HlChc
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:51:19 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 231 iterations in 0.057s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(t86_tops_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.50                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50                ( ![C:$i]:
% 0.20/0.50                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.50                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X22 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ((X22) = (k1_xboole_0))
% 0.20/0.50          | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50          | ~ (r1_tarski @ X22 @ sk_B)
% 0.20/0.50          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((![X22 : $i]:
% 0.20/0.50          (((X22) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X22 @ sk_B))) | 
% 0.20/0.50       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t44_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.50          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ X15)
% 0.20/0.50          | ~ (l1_pre_topc @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(t28_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.50         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(commutativity_k2_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]: ((k2_tarski @ X4 @ X3) = (k2_tarski @ X3 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.50  thf(t12_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.50         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k9_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.50           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((![X22 : $i]:
% 0.20/0.50          (((X22) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X22 @ sk_B)))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (((X22) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X22 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.50         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.50         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (((X22) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X22 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fc9_tops_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X13)
% 0.20/0.50          | ~ (v2_pre_topc @ X13)
% 0.20/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.50          | (v3_pre_topc @ (k1_tops_1 @ X13 @ X14) @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (((X22) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X22 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t84_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.50          | ((k1_tops_1 @ X21 @ X20) != (k1_xboole_0))
% 0.20/0.50          | (v2_tops_1 @ X20 @ X21)
% 0.20/0.50          | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (((X22) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X22 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (((X22) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X22 @ sk_B))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.50  thf('42', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (~
% 0.20/0.50       (![X22 : $i]:
% 0.20/0.50          (((X22) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X22 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X22 @ sk_B))) | 
% 0.20/0.50       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['42'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['46'])).
% 0.20/0.50  thf('48', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.50       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.50          | ~ (v2_tops_1 @ X20 @ X21)
% 0.20/0.50          | ((k1_tops_1 @ X21 @ X20) = (k1_xboole_0))
% 0.20/0.50          | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['42'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['46'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('split', [status(esa)], ['50'])).
% 0.20/0.50  thf(t56_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.50                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.50          | ~ (v3_pre_topc @ X17 @ X18)
% 0.20/0.50          | ~ (r1_tarski @ X17 @ X19)
% 0.20/0.50          | (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.50          | ~ (l1_pre_topc @ X18))),
% 0.20/0.50      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ sk_A)
% 0.20/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.50           | ~ (r1_tarski @ sk_C @ X0)
% 0.20/0.50           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.50           | ~ (r1_tarski @ sk_C @ X0)
% 0.20/0.50           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r1_tarski @ sk_C @ X0)
% 0.20/0.50           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.50         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['61', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.50         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.50         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.50             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['59', '68'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.20/0.50         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.50             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['58', '69'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((((k3_xboole_0 @ sk_C @ k1_xboole_0) = (sk_C)))
% 0.20/0.50         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.50             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('74', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['73', '76'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      ((((k1_xboole_0) = (sk_C)))
% 0.20/0.50         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.50             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['72', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['48'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((((sk_C) != (sk_C)))
% 0.20/0.50         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.50             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.50             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.20/0.50       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.50       ~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.20/0.50       (((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['80'])).
% 0.20/0.50  thf('82', plain, ($false),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['1', '44', '45', '47', '49', '51', '81'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
