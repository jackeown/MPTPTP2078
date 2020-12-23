%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L2UHfCT443

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:11 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 375 expanded)
%              Number of leaves         :   29 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          : 1089 (4555 expanded)
%              Number of equality atoms :   65 ( 128 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_pre_topc @ X23 @ X24 ) ) )
        = ( k2_pre_topc @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('16',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_C ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','14','15','16'])).

thf('18',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_C ) )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['17','24','25'])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_C ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_C
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('56',plain,
    ( sk_C
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','33','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('66',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['65','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['82','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','98'])).

thf('100',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ X20 )
       != ( k2_struct_0 @ X21 ) )
      | ( v1_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    ~ ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ~ ( v1_tops_1 @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('108',plain,(
    ~ ( v1_tops_1 @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('110',plain,(
    ~ ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['65','76'])).

thf('112',plain,(
    ~ ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','112'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L2UHfCT443
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:20:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 695 iterations in 0.256s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.52/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.52/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.52/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.71  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.52/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.52/0.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(t82_tops_1, conjecture,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ![C:$i]:
% 0.52/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71               ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.52/0.71                   ( v3_pre_topc @ C @ A ) ) =>
% 0.52/0.71                 ( v1_tops_1 @
% 0.52/0.71                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i]:
% 0.52/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.71          ( ![B:$i]:
% 0.52/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71              ( ![C:$i]:
% 0.52/0.71                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71                  ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.52/0.71                      ( v3_pre_topc @ C @ A ) ) =>
% 0.52/0.71                    ( v1_tops_1 @
% 0.52/0.71                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t82_tops_1])).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t41_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ![C:$i]:
% 0.52/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71               ( ( v3_pre_topc @ B @ A ) =>
% 0.52/0.71                 ( ( k2_pre_topc @
% 0.52/0.71                     A @ 
% 0.52/0.71                     ( k9_subset_1 @
% 0.52/0.71                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.52/0.71                   ( k2_pre_topc @
% 0.52/0.71                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.52/0.71          | ~ (v3_pre_topc @ X22 @ X23)
% 0.52/0.71          | ((k2_pre_topc @ X23 @ 
% 0.52/0.71              (k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.52/0.71               (k2_pre_topc @ X23 @ X24)))
% 0.52/0.71              = (k2_pre_topc @ X23 @ 
% 0.52/0.71                 (k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ X24)))
% 0.52/0.71          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.52/0.71          | ~ (l1_pre_topc @ X23)
% 0.52/0.71          | ~ (v2_pre_topc @ X23))),
% 0.52/0.71      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (v2_pre_topc @ sk_A)
% 0.52/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.71          | ((k2_pre_topc @ sk_A @ 
% 0.52/0.71              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.52/0.71               (k2_pre_topc @ sk_A @ X0)))
% 0.52/0.71              = (k2_pre_topc @ sk_A @ 
% 0.52/0.71                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 0.52/0.71          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.71  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(d3_struct_0, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X18 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(commutativity_k9_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.52/0.71          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))
% 0.52/0.71          | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['6', '9'])).
% 0.52/0.71  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(dt_l1_pre_topc, axiom,
% 0.52/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.71  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['10', '13'])).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['10', '13'])).
% 0.52/0.71  thf('16', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.71          | ((k2_pre_topc @ sk_A @ 
% 0.52/0.71              (k9_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.71               (k2_pre_topc @ sk_A @ X0) @ sk_C))
% 0.52/0.71              = (k2_pre_topc @ sk_A @ 
% 0.52/0.71                 (k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C))))),
% 0.52/0.71      inference('demod', [status(thm)], ['3', '4', '5', '14', '15', '16'])).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X18 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['18', '19'])).
% 0.52/0.71  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.71  thf(redefinition_k9_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.52/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.71          | ((k2_pre_topc @ sk_A @ 
% 0.52/0.71              (k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ sk_C))
% 0.52/0.71              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))))),
% 0.52/0.71      inference('demod', [status(thm)], ['17', '24', '25'])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (((k2_pre_topc @ sk_A @ 
% 0.52/0.71         (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_C))
% 0.52/0.71         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['0', '26'])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(d3_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ( v1_tops_1 @ B @ A ) <=>
% 0.52/0.71             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.52/0.71          | ~ (v1_tops_1 @ X20 @ X21)
% 0.52/0.71          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.52/0.71          | ~ (l1_pre_topc @ X21))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.52/0.71        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.71  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('32', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X18 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf(dt_k2_subset_1, axiom,
% 0.52/0.71    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.52/0.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.52/0.71  thf('36', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.52/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.52/0.71  thf('37', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.52/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.52/0.71          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.52/0.71  thf('40', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.52/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.52/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.52/0.71      inference('demod', [status(thm)], ['39', '42'])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('45', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.52/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.71  thf('46', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.52/0.71         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['43', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t3_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i]:
% 0.52/0.71         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('50', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.71  thf(t28_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('52', plain, (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.71  thf('53', plain, (((sk_C) = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.52/0.71      inference('demod', [status(thm)], ['47', '52'])).
% 0.52/0.71  thf('54', plain,
% 0.52/0.71      ((((sk_C) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '53'])).
% 0.52/0.71  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('56', plain, (((sk_C) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C))),
% 0.52/0.71      inference('demod', [status(thm)], ['54', '55'])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      (((k2_pre_topc @ sk_A @ sk_C)
% 0.52/0.71         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.71      inference('demod', [status(thm)], ['27', '33', '56'])).
% 0.52/0.71  thf('58', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.52/0.71          | ~ (v1_tops_1 @ X20 @ X21)
% 0.52/0.71          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.52/0.71          | ~ (l1_pre_topc @ X21))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | ((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))
% 0.52/0.71        | ~ (v1_tops_1 @ sk_C @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('62', plain, ((v1_tops_1 @ sk_C @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('63', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (((k2_struct_0 @ sk_A)
% 0.52/0.71         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.71      inference('demod', [status(thm)], ['57', '63'])).
% 0.52/0.71  thf('65', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.52/0.71           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      (![X18 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('68', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['66', '67'])).
% 0.52/0.71  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['68', '69'])).
% 0.52/0.71  thf('71', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.52/0.71          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.52/0.71  thf('72', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.52/0.71           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.52/0.71  thf('73', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['68', '69'])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.52/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.52/0.71           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X0 @ sk_B)
% 0.52/0.71           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['72', '75'])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['65', '76'])).
% 0.52/0.71  thf('78', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('79', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i]:
% 0.52/0.71         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('80', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['78', '79'])).
% 0.52/0.71  thf('81', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('82', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['80', '81'])).
% 0.52/0.71  thf('83', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.52/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.71  thf(dt_k9_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.52/0.71  thf('84', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.71         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.52/0.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.52/0.71  thf('85', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['83', '84'])).
% 0.52/0.71  thf('86', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.71  thf('87', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['85', '86'])).
% 0.52/0.71  thf('88', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.71         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.52/0.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.52/0.71  thf('89', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.52/0.71          (k1_zfmisc_1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.52/0.71  thf('90', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i]:
% 0.52/0.71         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('91', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (r1_tarski @ (k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['89', '90'])).
% 0.52/0.71  thf('92', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.52/0.71          (u1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['82', '91'])).
% 0.52/0.71  thf('93', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('94', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.71         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.52/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.71  thf('95', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.52/0.71           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['93', '94'])).
% 0.52/0.71  thf('96', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['92', '95'])).
% 0.52/0.71  thf('97', plain,
% 0.52/0.71      (![X15 : $i, X17 : $i]:
% 0.52/0.71         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('98', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.52/0.71          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['96', '97'])).
% 0.52/0.71  thf('99', plain,
% 0.52/0.71      ((m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.52/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['77', '98'])).
% 0.52/0.71  thf('100', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.52/0.71          | ((k2_pre_topc @ X21 @ X20) != (k2_struct_0 @ X21))
% 0.52/0.71          | (v1_tops_1 @ X20 @ X21)
% 0.52/0.71          | ~ (l1_pre_topc @ X21))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.52/0.71  thf('101', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 0.52/0.71        | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.52/0.71            != (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['99', '100'])).
% 0.52/0.71  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('103', plain,
% 0.52/0.71      (((v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 0.52/0.71        | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.52/0.71            != (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['101', '102'])).
% 0.52/0.71  thf('104', plain,
% 0.52/0.71      (![X18 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('105', plain,
% 0.52/0.71      (~ (v1_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('106', plain,
% 0.52/0.71      ((~ (v1_tops_1 @ (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.52/0.71           sk_A)
% 0.52/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['104', '105'])).
% 0.52/0.71  thf('107', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('108', plain,
% 0.52/0.71      (~ (v1_tops_1 @ (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.52/0.71      inference('demod', [status(thm)], ['106', '107'])).
% 0.52/0.71  thf('109', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X0 @ sk_B)
% 0.52/0.71           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['72', '75'])).
% 0.52/0.71  thf('110', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.52/0.71      inference('demod', [status(thm)], ['108', '109'])).
% 0.52/0.71  thf('111', plain,
% 0.52/0.71      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.71      inference('sup+', [status(thm)], ['65', '76'])).
% 0.52/0.71  thf('112', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.52/0.71      inference('demod', [status(thm)], ['110', '111'])).
% 0.52/0.71  thf('113', plain,
% 0.52/0.71      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.52/0.71         != (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('clc', [status(thm)], ['103', '112'])).
% 0.52/0.71  thf('114', plain, ($false),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['64', '113'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
