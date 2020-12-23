%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bNl2hLydM6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 136 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  621 (1947 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v4_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v4_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( v4_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v2_compts_1 @ X17 @ X18 )
      | ~ ( v8_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v2_compts_1 @ X17 @ X18 )
      | ~ ( v8_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_compts_1 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ~ ( v4_pre_topc @ X21 @ X20 )
      | ( v2_compts_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','55'])).

thf('57',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['30','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bNl2hLydM6
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 102 iterations in 0.059s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(t20_compts_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.20/0.51                   ( v2_compts_1 @ C @ A ) ) =>
% 0.20/0.51                 ( v2_compts_1 @
% 0.20/0.51                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.20/0.51                      ( v2_compts_1 @ C @ A ) ) =>
% 0.20/0.51                    ( v2_compts_1 @
% 0.20/0.51                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.51          sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.20/0.51           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(fc4_tops_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.51         ( v4_pre_topc @ C @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51       ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.51          | ~ (v4_pre_topc @ X14 @ X15)
% 0.20/0.51          | ~ (l1_pre_topc @ X15)
% 0.20/0.51          | ~ (v2_pre_topc @ X15)
% 0.20/0.51          | ~ (v4_pre_topc @ X16 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.51          | (v4_pre_topc @ (k3_xboole_0 @ X14 @ X16) @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc4_tops_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t16_compts_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.20/0.51             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | (v4_pre_topc @ X17 @ X18)
% 0.20/0.51          | ~ (v2_compts_1 @ X17 @ X18)
% 0.20/0.51          | ~ (v8_pre_topc @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X18)
% 0.20/0.51          | ~ (v2_pre_topc @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v8_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.20/0.51        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain, ((v8_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.20/0.51        | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | (v4_pre_topc @ X17 @ X18)
% 0.20/0.51          | ~ (v2_compts_1 @ X17 @ X18)
% 0.20/0.51          | ~ (v8_pre_topc @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X18)
% 0.20/0.51          | ~ (v2_pre_topc @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v8_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.51        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain, ((v8_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.20/0.51  thf('30', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k9_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.20/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.20/0.51           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.20/0.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t18_compts_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.51                   ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.51                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.51          | ~ (v2_compts_1 @ X19 @ X20)
% 0.20/0.51          | ~ (r1_tarski @ X21 @ X19)
% 0.20/0.51          | ~ (v4_pre_topc @ X21 @ X20)
% 0.20/0.51          | (v2_compts_1 @ X21 @ X20)
% 0.20/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.51          | ~ (l1_pre_topc @ X20)
% 0.20/0.51          | ~ (v2_pre_topc @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_compts_1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ sk_C)
% 0.20/0.51          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_compts_1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.20/0.51          | ~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.20/0.51          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '42'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.51      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X11 : $i, X13 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('47', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.51      inference('demod', [status(thm)], ['51', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.20/0.51          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '55'])).
% 0.20/0.51  thf('57', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '56'])).
% 0.20/0.51  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
