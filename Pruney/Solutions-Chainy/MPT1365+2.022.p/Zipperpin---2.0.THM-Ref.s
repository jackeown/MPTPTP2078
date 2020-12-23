%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DNl52dypIz

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:38 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 210 expanded)
%              Number of leaves         :   31 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  863 (3106 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X17 @ X15 )
        = ( k9_subset_1 @ X16 @ X17 @ ( k3_subset_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf('16',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
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

thf('27',plain,(
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

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','44'])).

thf('46',plain,
    ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    | ( v2_compts_1 @ ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X24 )
      | ~ ( v4_pre_topc @ X25 @ X24 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v4_pre_topc @ X26 @ X27 )
      | ~ ( v2_compts_1 @ X26 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('55',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52','60'])).

thf('62',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v4_pre_topc @ X26 @ X27 )
      | ~ ( v2_compts_1 @ X26 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('72',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['62','70','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('74',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['46','72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['4','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DNl52dypIz
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 712 iterations in 0.533s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.76/0.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.97  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.76/0.97  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.76/0.97  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.97  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.97  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(t20_compts_1, conjecture,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.76/0.97                   ( v2_compts_1 @ C @ A ) ) =>
% 0.76/0.97                 ( v2_compts_1 @
% 0.76/0.97                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i]:
% 0.76/0.97        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97          ( ![B:$i]:
% 0.76/0.97            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97              ( ![C:$i]:
% 0.76/0.97                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.76/0.97                      ( v2_compts_1 @ C @ A ) ) =>
% 0.76/0.97                    ( v2_compts_1 @
% 0.76/0.97                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.76/0.97          sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(redefinition_k9_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.76/0.97         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.76/0.97          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.76/0.97           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_k3_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.76/0.97          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.97  thf(t32_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ![C:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.76/0.97             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.76/0.97          | ((k7_subset_1 @ X16 @ X17 @ X15)
% 0.76/0.97              = (k9_subset_1 @ X16 @ X17 @ (k3_subset_1 @ X16 @ X15)))
% 0.76/0.97          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.76/0.97              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.76/0.97              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.76/0.97                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(involutiveness_k3_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X7 : $i, X8 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.76/0.97          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.76/0.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.97         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.76/0.97           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.76/0.97              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.76/0.97              = (k3_xboole_0 @ X0 @ sk_C)))),
% 0.76/0.97      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.97         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.76/0.97         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['5', '15'])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(redefinition_k7_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.76/0.97          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.76/0.97           = (k4_xboole_0 @ sk_B @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.76/0.97         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.76/0.97      inference('demod', [status(thm)], ['16', '19'])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_k7_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.76/0.97          | (m1_subset_1 @ (k7_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.76/0.97          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.76/0.97           = (k4_xboole_0 @ sk_B @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.76/0.97          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('demod', [status(thm)], ['23', '24'])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t18_compts_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.76/0.97                   ( v4_pre_topc @ C @ A ) ) =>
% 0.76/0.97                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.76/0.97          | ~ (v2_compts_1 @ X28 @ X29)
% 0.76/0.97          | ~ (r1_tarski @ X30 @ X28)
% 0.76/0.97          | ~ (v4_pre_topc @ X30 @ X29)
% 0.76/0.97          | (v2_compts_1 @ X30 @ X29)
% 0.76/0.97          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.76/0.97          | ~ (l1_pre_topc @ X29)
% 0.76/0.97          | ~ (v2_pre_topc @ X29))),
% 0.76/0.97      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v2_pre_topc @ sk_A)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v2_compts_1 @ X0 @ sk_A)
% 0.76/0.97          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.76/0.97          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.97          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.97  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('31', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v2_compts_1 @ X0 @ sk_A)
% 0.76/0.97          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.76/0.97          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.76/0.97          | ~ (v4_pre_topc @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.76/0.97          | (v2_compts_1 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['25', '32'])).
% 0.76/0.97  thf(dt_k2_subset_1, axiom,
% 0.76/0.97    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.76/0.97  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.76/0.97  thf('35', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.76/0.97      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.76/0.97  thf('36', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.76/0.97      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.76/0.97          | (m1_subset_1 @ (k7_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.97  thf(t3_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      (![X20 : $i, X21 : $i]:
% 0.76/0.97         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k7_subset_1 @ X0 @ X0 @ X1) @ X0)),
% 0.76/0.97      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.97  thf('41', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.76/0.97      inference('demod', [status(thm)], ['34', '35'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.76/0.97          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.76/0.97  thf('43', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.76/0.97      inference('demod', [status(thm)], ['40', '43'])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v4_pre_topc @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.76/0.97          | (v2_compts_1 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['33', '44'])).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      ((~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 0.76/0.97        | (v2_compts_1 @ 
% 0.76/0.97           (k4_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.76/0.97           sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '45'])).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('48', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t35_tops_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.76/0.97                 ( v4_pre_topc @
% 0.76/0.97                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.76/0.97  thf('49', plain,
% 0.76/0.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.97          | ~ (v4_pre_topc @ X23 @ X24)
% 0.76/0.97          | ~ (v4_pre_topc @ X25 @ X24)
% 0.76/0.97          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X25) @ 
% 0.76/0.97             X24)
% 0.76/0.97          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.97          | ~ (l1_pre_topc @ X24)
% 0.76/0.97          | ~ (v2_pre_topc @ X24))),
% 0.76/0.97      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v2_pre_topc @ sk_A)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.76/0.97          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['48', '49'])).
% 0.76/0.97  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t16_compts_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.97           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.76/0.97             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (![X26 : $i, X27 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.76/0.97          | (v4_pre_topc @ X26 @ X27)
% 0.76/0.97          | ~ (v2_compts_1 @ X26 @ X27)
% 0.76/0.97          | ~ (v8_pre_topc @ X27)
% 0.76/0.97          | ~ (l1_pre_topc @ X27)
% 0.76/0.97          | ~ (v2_pre_topc @ X27))),
% 0.76/0.97      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      ((~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | ~ (v8_pre_topc @ sk_A)
% 0.76/0.97        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.76/0.97        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['53', '54'])).
% 0.76/0.97  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('58', plain, ((v8_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('59', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('60', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.76/0.97  thf('61', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.97          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.76/0.97             sk_A)
% 0.76/0.97          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['50', '51', '52', '60'])).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.76/0.97        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.76/0.97           sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['47', '61'])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      (![X26 : $i, X27 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.76/0.97          | (v4_pre_topc @ X26 @ X27)
% 0.76/0.97          | ~ (v2_compts_1 @ X26 @ X27)
% 0.76/0.97          | ~ (v8_pre_topc @ X27)
% 0.76/0.97          | ~ (l1_pre_topc @ X27)
% 0.76/0.97          | ~ (v2_pre_topc @ X27))),
% 0.76/0.97      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.76/0.97  thf('65', plain,
% 0.76/0.97      ((~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | ~ (v8_pre_topc @ sk_A)
% 0.76/0.97        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.76/0.97        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.97  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('68', plain, ((v8_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('69', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('70', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.76/0.97           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf('72', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['62', '70', '71'])).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.76/0.97         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.76/0.97      inference('demod', [status(thm)], ['16', '19'])).
% 0.76/0.97  thf('74', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['46', '72', '73'])).
% 0.76/0.97  thf('75', plain, ($false), inference('demod', [status(thm)], ['4', '74'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
