%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e16VOmY9gy

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 148 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  678 (2048 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k9_subset_1 @ X34 @ X32 @ X33 )
        = ( k3_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k9_subset_1 @ X34 @ X32 @ X33 )
        = ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v2_compts_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v4_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( v4_pre_topc @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X40 @ X42 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc4_tops_1])).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v4_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( v4_pre_topc @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( v4_pre_topc @ ( k1_setfam_1 @ ( k2_tarski @ X40 @ X42 ) ) @ X41 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v4_pre_topc @ X43 @ X44 )
      | ~ ( v2_compts_1 @ X43 @ X44 )
      | ~ ( v8_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('17',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','22'])).

thf('24',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v4_pre_topc @ X43 @ X44 )
      | ~ ( v2_compts_1 @ X43 @ X44 )
      | ~ ( v8_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    v4_pre_topc @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['24','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X29 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v2_compts_1 @ X45 @ X46 )
      | ~ ( r1_tarski @ X47 @ X45 )
      | ~ ( v4_pre_topc @ X47 @ X46 )
      | ( v2_compts_1 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A )
      | ( v2_compts_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X28 ) @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('48',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('49',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X29 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k9_subset_1 @ X34 @ X32 @ X33 )
        = ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A )
      | ( v2_compts_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,(
    v2_compts_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ),
    inference('sup-',[status(thm)],['33','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['6','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e16VOmY9gy
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 138 iterations in 0.090s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.55  thf(t20_compts_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.21/0.55                   ( v2_compts_1 @ C @ A ) ) =>
% 0.21/0.55                 ( v2_compts_1 @
% 0.21/0.55                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.21/0.55                      ( v2_compts_1 @ C @ A ) ) =>
% 0.21/0.55                    ( v2_compts_1 @
% 0.21/0.55                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.21/0.55          sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.55         (((k9_subset_1 @ X34 @ X32 @ X33) = (k3_xboole_0 @ X32 @ X33))
% 0.21/0.55          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.55  thf(t12_setfam_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X35 : $i, X36 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.55         (((k9_subset_1 @ X34 @ X32 @ X33)
% 0.21/0.55            = (k1_setfam_1 @ (k2_tarski @ X32 @ X33)))
% 0.21/0.55          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.21/0.55           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (~ (v2_compts_1 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(fc4_tops_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.55         ( v4_pre_topc @ C @ A ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.55       ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.55          | ~ (v4_pre_topc @ X40 @ X41)
% 0.21/0.55          | ~ (l1_pre_topc @ X41)
% 0.21/0.55          | ~ (v2_pre_topc @ X41)
% 0.21/0.55          | ~ (v4_pre_topc @ X42 @ X41)
% 0.21/0.55          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.55          | (v4_pre_topc @ (k3_xboole_0 @ X40 @ X42) @ X41))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc4_tops_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X35 : $i, X36 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.55          | ~ (v4_pre_topc @ X40 @ X41)
% 0.21/0.55          | ~ (l1_pre_topc @ X41)
% 0.21/0.55          | ~ (v2_pre_topc @ X41)
% 0.21/0.55          | ~ (v4_pre_topc @ X42 @ X41)
% 0.21/0.55          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.21/0.55          | (v4_pre_topc @ (k1_setfam_1 @ (k2_tarski @ X40 @ X42)) @ X41))),
% 0.21/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v4_pre_topc @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.55  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t16_compts_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.21/0.55             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X43 : $i, X44 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.21/0.55          | (v4_pre_topc @ X43 @ X44)
% 0.21/0.55          | ~ (v2_compts_1 @ X43 @ X44)
% 0.21/0.55          | ~ (v8_pre_topc @ X44)
% 0.21/0.55          | ~ (l1_pre_topc @ X44)
% 0.21/0.55          | ~ (v2_pre_topc @ X44))),
% 0.21/0.55      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('20', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('21', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('22', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v4_pre_topc @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13', '14', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X43 : $i, X44 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.21/0.55          | (v4_pre_topc @ X43 @ X44)
% 0.21/0.55          | ~ (v2_compts_1 @ X43 @ X44)
% 0.21/0.55          | ~ (v8_pre_topc @ X44)
% 0.21/0.55          | ~ (l1_pre_topc @ X44)
% 0.21/0.55          | ~ (v2_pre_topc @ X44))),
% 0.21/0.55      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('30', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('31', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      ((v4_pre_topc @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k9_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k9_subset_1 @ X29 @ X30 @ X31) @ (k1_zfmisc_1 @ X29))
% 0.21/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X29)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.21/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.21/0.55           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ 
% 0.21/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t18_compts_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.21/0.55                   ( v4_pre_topc @ C @ A ) ) =>
% 0.21/0.55                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.21/0.55          | ~ (v2_compts_1 @ X45 @ X46)
% 0.21/0.55          | ~ (r1_tarski @ X47 @ X45)
% 0.21/0.55          | ~ (v4_pre_topc @ X47 @ X46)
% 0.21/0.55          | (v2_compts_1 @ X47 @ X46)
% 0.21/0.55          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.21/0.55          | ~ (l1_pre_topc @ X46)
% 0.21/0.55          | ~ (v2_pre_topc @ X46))),
% 0.21/0.55      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_pre_topc @ sk_A)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | (v2_compts_1 @ X0 @ sk_A)
% 0.21/0.55          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ sk_C)
% 0.21/0.55          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('44', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | (v2_compts_1 @ X0 @ sk_A)
% 0.21/0.55          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_C)
% 0.21/0.55          | ~ (v4_pre_topc @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A)
% 0.21/0.55          | (v2_compts_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['38', '45'])).
% 0.21/0.55  thf(dt_k2_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X28 : $i]: (m1_subset_1 @ (k2_subset_1 @ X28) @ (k1_zfmisc_1 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.55  thf('48', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.55  thf('49', plain, (![X28 : $i]: (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X28))),
% 0.21/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k9_subset_1 @ X29 @ X30 @ X31) @ (k1_zfmisc_1 @ X29))
% 0.21/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X29)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf(t3_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X37 : $i, X38 : $i]:
% 0.21/0.55         ((r1_tarski @ X37 @ X38) | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain, (![X28 : $i]: (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X28))),
% 0.21/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.55         (((k9_subset_1 @ X34 @ X32 @ X33)
% 0.21/0.55            = (k1_setfam_1 @ (k2_tarski @ X32 @ X33)))
% 0.21/0.55          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.21/0.55      inference('demod', [status(thm)], ['53', '56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v4_pre_topc @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A)
% 0.21/0.55          | (v2_compts_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['46', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((v2_compts_1 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '58'])).
% 0.21/0.55  thf('60', plain, ($false), inference('demod', [status(thm)], ['6', '59'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
