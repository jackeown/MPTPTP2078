%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9CLOpUrUrQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 131 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  604 (1481 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( v2_tex_2 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( v2_tex_2 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('47',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('49',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['26','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['4','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9CLOpUrUrQ
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:51:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 78 iterations in 0.040s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(t29_tex_2, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.22/0.51                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( l1_pre_topc @ A ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.22/0.51                    ( v2_tex_2 @
% 0.22/0.51                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.51         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.51           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.51  thf(commutativity_k2_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.51  thf(t12_setfam_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf(t48_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.22/0.51           = (k3_xboole_0 @ X2 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_k7_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.22/0.51          | (m1_subset_1 @ (k7_subset_1 @ X9 @ X8 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.22/0.51          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.22/0.51           = (k4_xboole_0 @ sk_C @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k4_xboole_0 @ sk_C @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['13', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['10', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['9', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t28_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.22/0.51                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.51          | ~ (v2_tex_2 @ X19 @ X20)
% 0.22/0.51          | ~ (r1_tarski @ X21 @ X19)
% 0.22/0.51          | (v2_tex_2 @ X21 @ X20)
% 0.22/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.51          | ~ (l1_pre_topc @ X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_C)
% 0.22/0.51          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_C)
% 0.22/0.51          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['25'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.22/0.51           = (k3_xboole_0 @ X2 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.22/0.51          | (m1_subset_1 @ (k7_subset_1 @ X9 @ X8 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.22/0.51          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.22/0.51           = (k4_xboole_0 @ sk_B @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['30', '33'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['27', '34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['25'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.51          | ~ (v2_tex_2 @ X19 @ X20)
% 0.22/0.51          | ~ (r1_tarski @ X21 @ X19)
% 0.22/0.51          | (v2_tex_2 @ X21 @ X20)
% 0.22/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.51          | ~ (l1_pre_topc @ X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.51  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      ((![X0 : $i]:
% 0.22/0.51          (~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51           | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.22/0.51         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['36', '41'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((![X0 : $i]:
% 0.22/0.51          ((v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.22/0.51           | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)))
% 0.22/0.51         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '42'])).
% 0.22/0.51  thf(t17_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.22/0.51         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.51  thf('46', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.51  thf('47', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.51  thf('48', plain, (((v2_tex_2 @ sk_C @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('split', [status(esa)], ['25'])).
% 0.22/0.51  thf('49', plain, (((v2_tex_2 @ sk_C @ sk_A))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.22/0.51  thf('50', plain, ((v2_tex_2 @ sk_C @ sk_A)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['26', '49'])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | (v2_tex_2 @ X0 @ sk_A)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '50'])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.22/0.51          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '51'])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.22/0.51      inference('sup+', [status(thm)], ['53', '54'])).
% 0.22/0.51  thf('56', plain, (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['52', '55'])).
% 0.22/0.51  thf('57', plain, ($false), inference('demod', [status(thm)], ['4', '56'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
