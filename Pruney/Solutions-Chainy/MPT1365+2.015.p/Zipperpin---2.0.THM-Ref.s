%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AewojxVWDb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 181 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  731 (2749 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t20_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v8_pre_topc @ A )
                  & ( v2_compts_1 @ B @ A )
                  & ( v2_compts_1 @ C @ A ) )
               => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v8_pre_topc @ A )
                    & ( v2_compts_1 @ B @ A )
                    & ( v2_compts_1 @ C @ A ) )
                 => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_compts_1])).

thf('0',plain,(
    ~ ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( v2_compts_1 @ X21 @ X22 )
      | ~ ( v8_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('28',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20','25','33'])).

thf('35',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( v2_compts_1 @ X21 @ X22 )
      | ~ ( v8_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('45',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','43','44'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X10 @ X12 )
        = ( k4_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_compts_1 @ X23 @ X24 )
      | ~ ( r1_tarski @ X25 @ X23 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v2_compts_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['45','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['14','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AewojxVWDb
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:47:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 93 iterations in 0.053s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(t20_compts_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.22/0.52                   ( v2_compts_1 @ C @ A ) ) =>
% 0.22/0.52                 ( v2_compts_1 @
% 0.22/0.52                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.22/0.52                      ( v2_compts_1 @ C @ A ) ) =>
% 0.22/0.52                    ( v2_compts_1 @
% 0.22/0.52                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.22/0.52          sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.52           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(commutativity_k9_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.52         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.52  thf('8', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.52         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.52           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.52  thf('14', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['8', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t35_tops_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.22/0.52                 ( v4_pre_topc @
% 0.22/0.52                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.52          | ~ (v4_pre_topc @ X18 @ X19)
% 0.22/0.52          | ~ (v4_pre_topc @ X20 @ X19)
% 0.22/0.52          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X20) @ 
% 0.22/0.52             X19)
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.52          | ~ (l1_pre_topc @ X19)
% 0.22/0.52          | ~ (v2_pre_topc @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.22/0.52             sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.52           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ X0 @ sk_B)
% 0.22/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t16_compts_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.22/0.52             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.52          | (v4_pre_topc @ X21 @ X22)
% 0.22/0.52          | ~ (v2_compts_1 @ X21 @ X22)
% 0.22/0.52          | ~ (v8_pre_topc @ X22)
% 0.22/0.52          | ~ (l1_pre_topc @ X22)
% 0.22/0.52          | ~ (v2_pre_topc @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('31', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('33', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '19', '20', '25', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.52          | (v4_pre_topc @ X21 @ X22)
% 0.22/0.52          | ~ (v2_compts_1 @ X21 @ X22)
% 0.22/0.52          | ~ (v8_pre_topc @ X22)
% 0.22/0.52          | ~ (l1_pre_topc @ X22)
% 0.22/0.52          | ~ (v2_pre_topc @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.22/0.52        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('43', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.52  thf('45', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['35', '43', '44'])).
% 0.22/0.52  thf(t48_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.22/0.52           = (k3_xboole_0 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k7_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.22/0.52          | (m1_subset_1 @ (k7_subset_1 @ X8 @ X7 @ X9) @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.22/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.22/0.52          | ((k7_subset_1 @ X11 @ X10 @ X12) = (k4_xboole_0 @ X10 @ X12)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.22/0.52           = (k4_xboole_0 @ sk_B @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.22/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['49', '52'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.22/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['46', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t18_compts_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.52                   ( v4_pre_topc @ C @ A ) ) =>
% 0.22/0.52                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.52          | ~ (v2_compts_1 @ X23 @ X24)
% 0.22/0.52          | ~ (r1_tarski @ X25 @ X23)
% 0.22/0.52          | ~ (v4_pre_topc @ X25 @ X24)
% 0.22/0.52          | (v2_compts_1 @ X25 @ X24)
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.52          | ~ (l1_pre_topc @ X24)
% 0.22/0.52          | ~ (v2_pre_topc @ X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v2_compts_1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.52          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.52          | (v2_compts_1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.22/0.52          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.52          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['54', '61'])).
% 0.22/0.52  thf(t17_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.52          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('65', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '64'])).
% 0.22/0.52  thf('66', plain, ($false), inference('demod', [status(thm)], ['14', '65'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
