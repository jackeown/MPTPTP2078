%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UPg4QBepDn

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 151 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  628 (1498 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t29_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tex_2 @ B @ A )
                  | ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v2_tex_2 @ B @ A )
                    | ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ sk_C @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ( v2_tex_2 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ( v2_tex_2 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('55',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('57',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['30','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['4','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UPg4QBepDn
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 138 iterations in 0.078s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(t29_tex_2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.21/0.56                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( l1_pre_topc @ A ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.21/0.56                    ( v2_tex_2 @
% 0.21/0.56                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.21/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.21/0.56           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t3_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('7', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf(dt_k2_subset_1, axiom,
% 0.21/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.56  thf('9', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.56  thf('10', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf(dt_k9_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k9_subset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 0.21/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf(t1_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.56       ( r1_tarski @ A @ C ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.56          | (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X2)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (r1_tarski @ (k9_subset_1 @ sk_C @ X0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['7', '16'])).
% 0.21/0.56  thf('18', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.21/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X19 : $i, X21 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.21/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t28_tex_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.56                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.56          | ~ (v2_tex_2 @ X22 @ X23)
% 0.21/0.56          | ~ (r1_tarski @ X24 @ X22)
% 0.21/0.56          | (v2_tex_2 @ X24 @ X23)
% 0.21/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.56          | ~ (l1_pre_topc @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ sk_C)
% 0.21/0.56          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ sk_C)
% 0.21/0.56          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['29'])).
% 0.21/0.56  thf(t48_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.21/0.56           = (k3_xboole_0 @ X5 @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('34', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf(t36_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.21/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.56          | (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X19 : $i, X21 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.21/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.21/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['31', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['29'])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.56          | ~ (v2_tex_2 @ X22 @ X23)
% 0.21/0.56          | ~ (r1_tarski @ X24 @ X22)
% 0.21/0.56          | (v2_tex_2 @ X24 @ X23)
% 0.21/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.56          | ~ (l1_pre_topc @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ sk_A)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.56           | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.56         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['42', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.21/0.56           | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)))
% 0.21/0.56         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['41', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.21/0.56           = (k3_xboole_0 @ X5 @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.21/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.21/0.56      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.21/0.56         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '52'])).
% 0.21/0.56  thf('54', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.56  thf('55', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain, (((v2_tex_2 @ sk_C @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.56      inference('split', [status(esa)], ['29'])).
% 0.21/0.56  thf('57', plain, (((v2_tex_2 @ sk_C @ sk_A))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.21/0.56  thf('58', plain, ((v2_tex_2 @ sk_C @ sk_A)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['30', '57'])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.21/0.56          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['28', '58'])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.21/0.56          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '59'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.56  thf('64', plain, (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['60', '63'])).
% 0.21/0.56  thf('65', plain, ($false), inference('demod', [status(thm)], ['4', '64'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
