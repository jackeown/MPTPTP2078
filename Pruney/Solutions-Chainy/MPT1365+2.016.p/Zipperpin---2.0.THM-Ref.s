%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HbI3IctAv0

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
% Statistics : Number of formulae       :   89 ( 236 expanded)
%              Number of leaves         :   22 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  703 (3653 expanded)
%              Number of equality atoms :   20 (  72 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

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
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_B )
    | ( v2_compts_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ~ ( v4_pre_topc @ X15 @ X14 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38','43','51'])).

thf('53',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('56',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('63',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['53','61','62'])).

thf('64',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['29','30','31','32','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['14','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HbI3IctAv0
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 96 iterations in 0.064s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.22/0.54  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.22/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(t20_compts_1, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.22/0.54                   ( v2_compts_1 @ C @ A ) ) =>
% 0.22/0.54                 ( v2_compts_1 @
% 0.22/0.54                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54              ( ![C:$i]:
% 0.22/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.22/0.54                      ( v2_compts_1 @ C @ A ) ) =>
% 0.22/0.54                    ( v2_compts_1 @
% 0.22/0.54                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.22/0.54          sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k9_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.22/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(commutativity_k9_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.22/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.54         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.54  thf('8', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.22/0.54         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.22/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.54  thf('14', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '13'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_k9_subset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.54       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.54         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.22/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.22/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.22/0.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t18_compts_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.54                   ( v4_pre_topc @ C @ A ) ) =>
% 0.22/0.54                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.54          | ~ (v2_compts_1 @ X18 @ X19)
% 0.22/0.54          | ~ (r1_tarski @ X20 @ X18)
% 0.22/0.54          | ~ (v4_pre_topc @ X20 @ X19)
% 0.22/0.54          | (v2_compts_1 @ X20 @ X19)
% 0.22/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.54          | ~ (l1_pre_topc @ X19)
% 0.22/0.54          | ~ (v2_pre_topc @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v2_pre_topc @ sk_A)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_compts_1 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.54          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.54  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('26', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v2_compts_1 @ X0 @ sk_A)
% 0.22/0.54          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.54          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 0.22/0.54          | ~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.22/0.54          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '27'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_B)
% 0.22/0.54        | (v2_compts_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.54        | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '28'])).
% 0.22/0.54  thf(t17_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t35_tops_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.22/0.54                 ( v4_pre_topc @
% 0.22/0.54                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (v4_pre_topc @ X13 @ X14)
% 0.22/0.54          | ~ (v4_pre_topc @ X15 @ X14)
% 0.22/0.54          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ X15) @ 
% 0.22/0.54             X14)
% 0.22/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (l1_pre_topc @ X14)
% 0.22/0.54          | ~ (v2_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v2_pre_topc @ sk_A)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.22/0.54             sk_A)
% 0.22/0.54          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.54          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.54  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.54         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.22/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.22/0.54           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ X0 @ sk_B)
% 0.22/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t16_compts_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.22/0.54             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | (v4_pre_topc @ X16 @ X17)
% 0.22/0.54          | ~ (v2_compts_1 @ X16 @ X17)
% 0.22/0.54          | ~ (v8_pre_topc @ X17)
% 0.22/0.54          | ~ (l1_pre_topc @ X17)
% 0.22/0.54          | ~ (v2_pre_topc @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.22/0.54        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.54  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('49', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('50', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('51', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.22/0.54          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '37', '38', '43', '51'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.22/0.54        | (v4_pre_topc @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['33', '52'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.54          | (v4_pre_topc @ X16 @ X17)
% 0.22/0.54          | ~ (v2_compts_1 @ X16 @ X17)
% 0.22/0.54          | ~ (v8_pre_topc @ X17)
% 0.22/0.54          | ~ (l1_pre_topc @ X17)
% 0.22/0.54          | ~ (v2_pre_topc @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v8_pre_topc @ sk_A)
% 0.22/0.54        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.22/0.54        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.54  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('59', plain, ((v8_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('60', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('61', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.54  thf('63', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['53', '61', '62'])).
% 0.22/0.54  thf('64', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['29', '30', '31', '32', '63'])).
% 0.22/0.54  thf('65', plain, ($false), inference('demod', [status(thm)], ['14', '64'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
