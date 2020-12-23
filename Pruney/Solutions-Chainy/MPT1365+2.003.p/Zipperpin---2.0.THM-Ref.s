%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R00FhFh1k9

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:35 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 152 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  710 (2234 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X24 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
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
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v4_pre_topc @ X26 @ X27 )
      | ~ ( v2_compts_1 @ X26 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
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
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v4_pre_topc @ X26 @ X27 )
      | ~ ( v2_compts_1 @ X26 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
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
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('31',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['21','29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('34',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X19 @ X18 ) )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','49','50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_compts_1 @ X28 @ X29 )
      | ~ ( r1_tarski @ X30 @ X28 )
      | ~ ( v4_pre_topc @ X30 @ X29 )
      | ( v2_compts_1 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['31','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['4','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R00FhFh1k9
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 684 iterations in 0.290s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.55/0.74  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.55/0.74  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.55/0.74  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.55/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(t20_compts_1, conjecture,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.55/0.74                   ( v2_compts_1 @ C @ A ) ) =>
% 0.55/0.74                 ( v2_compts_1 @
% 0.55/0.74                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i]:
% 0.55/0.74        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74          ( ![B:$i]:
% 0.55/0.74            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74              ( ![C:$i]:
% 0.55/0.74                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.55/0.74                      ( v2_compts_1 @ C @ A ) ) =>
% 0.55/0.74                    ( v2_compts_1 @
% 0.55/0.74                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.74          sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(redefinition_k9_subset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.74         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.55/0.74          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.55/0.74           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t35_tops_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.55/0.74                 ( v4_pre_topc @
% 0.55/0.74                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.55/0.74          | ~ (v4_pre_topc @ X23 @ X24)
% 0.55/0.74          | ~ (v4_pre_topc @ X25 @ X24)
% 0.55/0.74          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X25) @ 
% 0.55/0.74             X24)
% 0.55/0.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.55/0.74          | ~ (l1_pre_topc @ X24)
% 0.55/0.74          | ~ (v2_pre_topc @ X24))),
% 0.55/0.74      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.55/0.74             sk_A)
% 0.55/0.74          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.74  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.55/0.74             sk_A)
% 0.55/0.74          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t16_compts_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.55/0.74             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.55/0.74          | (v4_pre_topc @ X26 @ X27)
% 0.55/0.74          | ~ (v2_compts_1 @ X26 @ X27)
% 0.55/0.74          | ~ (v8_pre_topc @ X27)
% 0.55/0.74          | ~ (l1_pre_topc @ X27)
% 0.55/0.74          | ~ (v2_pre_topc @ X27))),
% 0.55/0.74      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      ((~ (v2_pre_topc @ sk_A)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v8_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.55/0.74        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.74  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('17', plain, ((v8_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('18', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('19', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.55/0.74             sk_A)
% 0.55/0.74          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '19'])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.55/0.74        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.74           sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['5', '20'])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.55/0.74          | (v4_pre_topc @ X26 @ X27)
% 0.55/0.74          | ~ (v2_compts_1 @ X26 @ X27)
% 0.55/0.74          | ~ (v8_pre_topc @ X27)
% 0.55/0.74          | ~ (l1_pre_topc @ X27)
% 0.55/0.74          | ~ (v2_pre_topc @ X27))),
% 0.55/0.74      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      ((~ (v2_pre_topc @ sk_A)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v8_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.55/0.74        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.74  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('27', plain, ((v8_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('28', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('29', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.55/0.74           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('31', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['21', '29', '30'])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_k1_pre_topc, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( l1_pre_topc @ A ) & 
% 0.55/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.74       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.55/0.74         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X16)
% 0.55/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.55/0.74          | (m1_pre_topc @ (k1_pre_topc @ X16 @ X17) @ X16))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('36', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['34', '35'])).
% 0.55/0.74  thf(t48_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      (![X4 : $i, X5 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.55/0.74           = (k3_xboole_0 @ X4 @ X5))),
% 0.55/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.74  thf(t36_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.55/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.55/0.74      inference('sup+', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf(t3_subset, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X13 : $i, X15 : $i]:
% 0.55/0.74         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.74  thf(t39_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.55/0.74               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X20 @ X21)
% 0.55/0.74          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.55/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.55/0.74          | ~ (l1_pre_topc @ X21))),
% 0.55/0.74      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X2)
% 0.55/0.74          | (m1_subset_1 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ X2))),
% 0.55/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((m1_subset_1 @ 
% 0.55/0.74           (k3_xboole_0 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ X0) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['36', '43'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t29_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.55/0.74          | ((u1_struct_0 @ (k1_pre_topc @ X19 @ X18)) = (X18))
% 0.55/0.74          | ~ (l1_pre_topc @ X19))),
% 0.55/0.74      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.55/0.74  thf('47', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.55/0.74  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('49', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['47', '48'])).
% 0.55/0.74  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.55/0.74          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['44', '49', '50'])).
% 0.55/0.74  thf('52', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t18_compts_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.55/0.74                   ( v4_pre_topc @ C @ A ) ) =>
% 0.55/0.74                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.55/0.74  thf('53', plain,
% 0.55/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.55/0.74          | ~ (v2_compts_1 @ X28 @ X29)
% 0.55/0.74          | ~ (r1_tarski @ X30 @ X28)
% 0.55/0.74          | ~ (v4_pre_topc @ X30 @ X29)
% 0.55/0.74          | (v2_compts_1 @ X30 @ X29)
% 0.55/0.74          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.55/0.74          | ~ (l1_pre_topc @ X29)
% 0.55/0.74          | ~ (v2_pre_topc @ X29))),
% 0.55/0.74      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.55/0.74  thf('54', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74          | (v2_compts_1 @ X0 @ sk_A)
% 0.55/0.74          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.55/0.74          | ~ (r1_tarski @ X0 @ sk_B)
% 0.55/0.74          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.74  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('57', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('58', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.75          | (v2_compts_1 @ X0 @ sk_A)
% 0.55/0.75          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.55/0.75          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.55/0.75  thf('59', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.55/0.75          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.55/0.75          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['51', '58'])).
% 0.55/0.75  thf('60', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.55/0.75      inference('sup+', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('61', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.55/0.75          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['59', '60'])).
% 0.55/0.75  thf('62', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['31', '61'])).
% 0.55/0.75  thf('63', plain, ($false), inference('demod', [status(thm)], ['4', '62'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
