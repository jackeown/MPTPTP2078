%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zX9ABZCVJw

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:10 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 275 expanded)
%              Number of leaves         :   27 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  822 (3186 expanded)
%              Number of equality atoms :   46 (  77 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t82_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( v1_tops_1 @ C @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v1_tops_1 @ B @ A )
                    & ( v1_tops_1 @ C @ A )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_tops_1])).

thf('1',plain,(
    ~ ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v1_tops_1 @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_tops_1 @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t81_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X24 )
        = ( k2_pre_topc @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X24 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t81_tops_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k2_pre_topc @ X0 @ X2 )
        = ( k2_pre_topc @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_tops_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('46',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','41','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_tops_1 @ sk_C @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','60','61','62'])).

thf('64',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('70',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k2_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('75',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ X20 )
       != ( k2_struct_0 @ X21 ) )
      | ( v1_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ X1 @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','85'])).

thf('87',plain,(
    v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['14','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zX9ABZCVJw
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 857 iterations in 0.525s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.97  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.76/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.97  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.97  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(d3_struct_0, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf(t82_tops_1, conjecture,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97               ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.76/0.97                   ( v3_pre_topc @ C @ A ) ) =>
% 0.76/0.97                 ( v1_tops_1 @
% 0.76/0.97                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i]:
% 0.76/0.97        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97          ( ![B:$i]:
% 0.76/0.97            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97              ( ![C:$i]:
% 0.76/0.97                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97                  ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.76/0.97                      ( v3_pre_topc @ C @ A ) ) =>
% 0.76/0.97                    ( v1_tops_1 @
% 0.76/0.97                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t82_tops_1])).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      (~ (v1_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      ((~ (v1_tops_1 @ (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.76/0.97           sk_A)
% 0.76/0.97        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.97  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_l1_pre_topc, axiom,
% 0.76/0.97    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.76/0.97  thf('4', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.97  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (~ (v1_tops_1 @ (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['2', '5'])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.76/0.97        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.76/0.97      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.97  thf(redefinition_k9_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.97         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.76/0.97          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.76/0.97           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.97  thf('14', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['6', '13'])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.76/0.97      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.76/0.97        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.76/0.97      inference('demod', [status(thm)], ['18', '19'])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf(t81_tops_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ( v1_tops_1 @ B @ A ) =>
% 0.76/0.97             ( ![C:$i]:
% 0.76/0.97               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97                 ( ( v3_pre_topc @ C @ A ) =>
% 0.76/0.97                   ( ( k2_pre_topc @ A @ C ) =
% 0.76/0.97                     ( k2_pre_topc @
% 0.76/0.97                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.76/0.97          | ~ (v3_pre_topc @ X24 @ X23)
% 0.76/0.97          | ((k2_pre_topc @ X23 @ X24)
% 0.76/0.97              = (k2_pre_topc @ X23 @ 
% 0.76/0.97                 (k9_subset_1 @ (u1_struct_0 @ X23) @ X24 @ X22)))
% 0.76/0.97          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.76/0.97          | ~ (v1_tops_1 @ X22 @ X23)
% 0.76/0.97          | ~ (l1_pre_topc @ X23)
% 0.76/0.97          | ~ (v2_pre_topc @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [t81_tops_1])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.76/0.97          | ~ (l1_struct_0 @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v1_tops_1 @ X1 @ X0)
% 0.76/0.97          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.76/0.97          | ((k2_pre_topc @ X0 @ X2)
% 0.76/0.97              = (k2_pre_topc @ X0 @ 
% 0.76/0.97                 (k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ X1)))
% 0.76/0.97          | ~ (v3_pre_topc @ X2 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v3_pre_topc @ X0 @ sk_A)
% 0.76/0.97          | ((k2_pre_topc @ sk_A @ X0)
% 0.76/0.97              = (k2_pre_topc @ sk_A @ 
% 0.76/0.97                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | ~ (v1_tops_1 @ sk_B @ sk_A)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '23'])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t3_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i]:
% 0.76/0.97         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('28', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['25', '28'])).
% 0.76/0.97  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('31', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.97  thf(t12_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i]:
% 0.76/0.97         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      (((k2_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf('35', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i]:
% 0.76/0.97         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (((k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      ((((k2_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.76/0.97        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['34', '37'])).
% 0.76/0.97  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (((k2_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['38', '39'])).
% 0.76/0.97  thf('41', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['33', '40'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.76/0.97      inference('demod', [status(thm)], ['18', '19'])).
% 0.76/0.97  thf('43', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.76/0.97         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.76/0.97          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.76/0.97           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['42', '43'])).
% 0.76/0.97  thf('45', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['33', '40'])).
% 0.76/0.97  thf('46', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v3_pre_topc @ X0 @ sk_A)
% 0.76/0.97          | ((k2_pre_topc @ sk_A @ X0)
% 0.76/0.97              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['24', '41', '44', '45', '46', '47', '48', '49'])).
% 0.76/0.97  thf('51', plain,
% 0.76/0.97      ((((k2_pre_topc @ sk_A @ sk_C)
% 0.76/0.97          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))
% 0.76/0.97        | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['15', '50'])).
% 0.76/0.97  thf('52', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.76/0.97      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf(d3_tops_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( l1_pre_topc @ A ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ( v1_tops_1 @ B @ A ) <=>
% 0.76/0.97             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (![X20 : $i, X21 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.76/0.97          | ~ (v1_tops_1 @ X20 @ X21)
% 0.76/0.97          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.76/0.97          | ~ (l1_pre_topc @ X21))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.76/0.97          | ~ (l1_struct_0 @ X0)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ((k2_pre_topc @ X0 @ X1) = (k2_struct_0 @ X0))
% 0.76/0.97          | ~ (v1_tops_1 @ X1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['53', '54'])).
% 0.76/0.97  thf('56', plain,
% 0.76/0.97      ((~ (v1_tops_1 @ sk_C @ sk_A)
% 0.76/0.97        | ((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['52', '55'])).
% 0.76/0.97  thf('57', plain, ((v1_tops_1 @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('60', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.76/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.97  thf('61', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf('62', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      (((k2_struct_0 @ sk_A)
% 0.76/0.97         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.76/0.97      inference('demod', [status(thm)], ['51', '60', '61', '62'])).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf('65', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('66', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i]:
% 0.76/0.97         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('67', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['65', '66'])).
% 0.76/0.97  thf('68', plain,
% 0.76/0.97      (((r1_tarski @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['64', '67'])).
% 0.76/0.97  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('70', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['68', '69'])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i]:
% 0.76/0.97         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.97  thf('72', plain,
% 0.76/0.97      (((k2_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['70', '71'])).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.97  thf(t29_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.97         (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ (k2_xboole_0 @ X4 @ X6))),
% 0.76/0.97      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      (![X13 : $i, X15 : $i]:
% 0.76/0.97         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('76', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X2) @ 
% 0.76/0.97          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['74', '75'])).
% 0.76/0.97  thf('77', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.76/0.97          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['73', '76'])).
% 0.76/0.97  thf('78', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.76/0.97          (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['72', '77'])).
% 0.76/0.97  thf('79', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      (![X20 : $i, X21 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.76/0.97          | ((k2_pre_topc @ X21 @ X20) != (k2_struct_0 @ X21))
% 0.76/0.97          | (v1_tops_1 @ X20 @ X21)
% 0.76/0.97          | ~ (l1_pre_topc @ X21))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.76/0.97  thf('81', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.76/0.97          | ~ (l1_struct_0 @ X0)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | (v1_tops_1 @ X1 @ X0)
% 0.76/0.97          | ((k2_pre_topc @ X0 @ X1) != (k2_struct_0 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['79', '80'])).
% 0.76/0.97  thf('82', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))
% 0.76/0.97            != (k2_struct_0 @ sk_A))
% 0.76/0.97          | (v1_tops_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['78', '81'])).
% 0.76/0.97  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('85', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))
% 0.76/0.97            != (k2_struct_0 @ sk_A))
% 0.76/0.97          | (v1_tops_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.76/0.97  thf('86', plain,
% 0.76/0.97      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.76/0.97        | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['63', '85'])).
% 0.76/0.97  thf('87', plain, ((v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.97      inference('simplify', [status(thm)], ['86'])).
% 0.76/0.97  thf('88', plain, ($false), inference('demod', [status(thm)], ['14', '87'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
