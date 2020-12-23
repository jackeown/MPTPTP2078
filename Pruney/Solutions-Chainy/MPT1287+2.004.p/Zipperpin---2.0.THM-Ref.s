%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQaoWIWbJw

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:57 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 138 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  791 (1945 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t109_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v6_tops_1 @ B @ A )
                  & ( v6_tops_1 @ C @ A ) )
               => ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v6_tops_1 @ B @ A )
                    & ( v6_tops_1 @ C @ A ) )
                 => ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t109_tops_1])).

thf('0',plain,(
    ~ ( v6_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v6_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t108_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v5_tops_1 @ B @ A )
                  & ( v5_tops_1 @ C @ A ) )
               => ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v5_tops_1 @ X21 @ X22 )
      | ~ ( v5_tops_1 @ X23 @ X22 )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X23 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t108_tops_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ X0 @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t101_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v6_tops_1 @ X19 @ X20 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14','20'])).

thf('22',plain,
    ( ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v6_tops_1 @ X19 @ X20 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v6_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k3_subset_1 @ X14 @ ( k7_subset_1 @ X14 @ X15 @ X13 ) )
        = ( k4_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X15 ) @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X12 @ X10 )
        = ( k9_subset_1 @ X11 @ X12 @ ( k3_subset_1 @ X11 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','44'])).

thf('46',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['29','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v6_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v6_tops_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v6_tops_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v6_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['4','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQaoWIWbJw
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.02/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.24  % Solved by: fo/fo7.sh
% 1.02/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.24  % done 982 iterations in 0.776s
% 1.02/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.24  % SZS output start Refutation
% 1.02/1.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.02/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.24  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 1.02/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.24  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.02/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.24  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.02/1.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.24  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.02/1.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.02/1.24  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.02/1.24  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.02/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.02/1.24  thf(t109_tops_1, conjecture,
% 1.02/1.24    (![A:$i]:
% 1.02/1.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.24       ( ![B:$i]:
% 1.02/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.24           ( ![C:$i]:
% 1.02/1.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.24               ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 1.02/1.24                 ( v6_tops_1 @
% 1.02/1.24                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 1.02/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.24    (~( ![A:$i]:
% 1.02/1.24        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.24          ( ![B:$i]:
% 1.02/1.24            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.24              ( ![C:$i]:
% 1.02/1.24                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.24                  ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 1.02/1.24                    ( v6_tops_1 @
% 1.02/1.24                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 1.02/1.24    inference('cnf.neg', [status(esa)], [t109_tops_1])).
% 1.02/1.24  thf('0', plain,
% 1.02/1.24      (~ (v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('1', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf(redefinition_k9_subset_1, axiom,
% 1.02/1.24    (![A:$i,B:$i,C:$i]:
% 1.02/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.24       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.02/1.24  thf('2', plain,
% 1.02/1.24      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.02/1.24         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 1.02/1.24          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.02/1.24      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.02/1.24  thf('3', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.02/1.24           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.02/1.24      inference('sup-', [status(thm)], ['1', '2'])).
% 1.02/1.24  thf('4', plain, (~ (v6_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 1.02/1.24      inference('demod', [status(thm)], ['0', '3'])).
% 1.02/1.24  thf('5', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf(dt_k3_subset_1, axiom,
% 1.02/1.24    (![A:$i,B:$i]:
% 1.02/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.24       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.02/1.24  thf('6', plain,
% 1.02/1.24      (![X3 : $i, X4 : $i]:
% 1.02/1.24         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 1.02/1.24          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 1.02/1.24      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.02/1.24  thf('7', plain,
% 1.02/1.24      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.02/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.24  thf('8', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('9', plain,
% 1.02/1.24      (![X3 : $i, X4 : $i]:
% 1.02/1.24         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 1.02/1.24          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 1.02/1.24      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.02/1.24  thf('10', plain,
% 1.02/1.24      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('sup-', [status(thm)], ['8', '9'])).
% 1.02/1.24  thf(t108_tops_1, axiom,
% 1.02/1.24    (![A:$i]:
% 1.02/1.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.24       ( ![B:$i]:
% 1.02/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.24           ( ![C:$i]:
% 1.02/1.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.24               ( ( ( v5_tops_1 @ B @ A ) & ( v5_tops_1 @ C @ A ) ) =>
% 1.02/1.24                 ( v5_tops_1 @
% 1.02/1.24                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 1.02/1.24  thf('11', plain,
% 1.02/1.24      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.02/1.24          | ~ (v5_tops_1 @ X21 @ X22)
% 1.02/1.24          | ~ (v5_tops_1 @ X23 @ X22)
% 1.02/1.24          | (v5_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X23) @ X22)
% 1.02/1.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.02/1.24          | ~ (l1_pre_topc @ X22)
% 1.02/1.24          | ~ (v2_pre_topc @ X22))),
% 1.02/1.24      inference('cnf', [status(esa)], [t108_tops_1])).
% 1.02/1.24  thf('12', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (~ (v2_pre_topc @ sk_A)
% 1.02/1.24          | ~ (l1_pre_topc @ sk_A)
% 1.02/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.24          | (v5_tops_1 @ 
% 1.02/1.24             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 1.02/1.24             sk_A)
% 1.02/1.24          | ~ (v5_tops_1 @ X0 @ sk_A)
% 1.02/1.24          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.02/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.02/1.24  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('15', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf(t101_tops_1, axiom,
% 1.02/1.24    (![A:$i]:
% 1.02/1.24     ( ( l1_pre_topc @ A ) =>
% 1.02/1.24       ( ![B:$i]:
% 1.02/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.24           ( ( v6_tops_1 @ B @ A ) <=>
% 1.02/1.24             ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.02/1.24  thf('16', plain,
% 1.02/1.24      (![X19 : $i, X20 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.02/1.24          | ~ (v6_tops_1 @ X19 @ X20)
% 1.02/1.24          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 1.02/1.24          | ~ (l1_pre_topc @ X20))),
% 1.02/1.24      inference('cnf', [status(esa)], [t101_tops_1])).
% 1.02/1.24  thf('17', plain,
% 1.02/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.24        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.02/1.24        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 1.02/1.24      inference('sup-', [status(thm)], ['15', '16'])).
% 1.02/1.24  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('19', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('20', plain,
% 1.02/1.24      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.02/1.24      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.02/1.24  thf('21', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.24          | (v5_tops_1 @ 
% 1.02/1.24             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 1.02/1.24             sk_A)
% 1.02/1.24          | ~ (v5_tops_1 @ X0 @ sk_A))),
% 1.02/1.24      inference('demod', [status(thm)], ['12', '13', '14', '20'])).
% 1.02/1.24  thf('22', plain,
% 1.02/1.24      ((~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 1.02/1.24        | (v5_tops_1 @ 
% 1.02/1.24           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.24            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.02/1.24           sk_A))),
% 1.02/1.24      inference('sup-', [status(thm)], ['7', '21'])).
% 1.02/1.24  thf('23', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('24', plain,
% 1.02/1.24      (![X19 : $i, X20 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.02/1.24          | ~ (v6_tops_1 @ X19 @ X20)
% 1.02/1.24          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 1.02/1.24          | ~ (l1_pre_topc @ X20))),
% 1.02/1.24      inference('cnf', [status(esa)], [t101_tops_1])).
% 1.02/1.24  thf('25', plain,
% 1.02/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.24        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 1.02/1.24        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 1.02/1.24      inference('sup-', [status(thm)], ['23', '24'])).
% 1.02/1.24  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('27', plain, ((v6_tops_1 @ sk_C @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('28', plain,
% 1.02/1.24      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 1.02/1.24      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.02/1.24  thf('29', plain,
% 1.02/1.24      ((v5_tops_1 @ 
% 1.02/1.24        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.24         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.02/1.24        sk_A)),
% 1.02/1.24      inference('demod', [status(thm)], ['22', '28'])).
% 1.02/1.24  thf('30', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('31', plain,
% 1.02/1.24      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.02/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.24  thf(t33_subset_1, axiom,
% 1.02/1.24    (![A:$i,B:$i]:
% 1.02/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.24       ( ![C:$i]:
% 1.02/1.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.24           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 1.02/1.24             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 1.02/1.24  thf('32', plain,
% 1.02/1.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.02/1.24          | ((k3_subset_1 @ X14 @ (k7_subset_1 @ X14 @ X15 @ X13))
% 1.02/1.24              = (k4_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X15) @ X13))
% 1.02/1.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 1.02/1.24      inference('cnf', [status(esa)], [t33_subset_1])).
% 1.02/1.24  thf('33', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.24          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.02/1.24               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.02/1.24              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.02/1.24                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.02/1.24      inference('sup-', [status(thm)], ['31', '32'])).
% 1.02/1.24  thf('34', plain,
% 1.02/1.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.24          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.02/1.24         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.24            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.02/1.24      inference('sup-', [status(thm)], ['30', '33'])).
% 1.02/1.24  thf('35', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('36', plain,
% 1.02/1.24      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.02/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.24  thf(t32_subset_1, axiom,
% 1.02/1.24    (![A:$i,B:$i]:
% 1.02/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.24       ( ![C:$i]:
% 1.02/1.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.24           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.02/1.24             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.02/1.24  thf('37', plain,
% 1.02/1.24      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.02/1.24          | ((k7_subset_1 @ X11 @ X12 @ X10)
% 1.02/1.24              = (k9_subset_1 @ X11 @ X12 @ (k3_subset_1 @ X11 @ X10)))
% 1.02/1.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.02/1.24      inference('cnf', [status(esa)], [t32_subset_1])).
% 1.02/1.24  thf('38', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.24          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.02/1.24              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.02/1.24              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.02/1.24                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.02/1.24      inference('sup-', [status(thm)], ['36', '37'])).
% 1.02/1.24  thf('39', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf(involutiveness_k3_subset_1, axiom,
% 1.02/1.24    (![A:$i,B:$i]:
% 1.02/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.24       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.02/1.24  thf('40', plain,
% 1.02/1.24      (![X5 : $i, X6 : $i]:
% 1.02/1.24         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 1.02/1.24          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.02/1.24      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.02/1.24  thf('41', plain,
% 1.02/1.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 1.02/1.24      inference('sup-', [status(thm)], ['39', '40'])).
% 1.02/1.24  thf('42', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.02/1.24           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.02/1.24      inference('sup-', [status(thm)], ['1', '2'])).
% 1.02/1.24  thf('43', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.24          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.02/1.24              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.02/1.24              = (k3_xboole_0 @ X0 @ sk_C)))),
% 1.02/1.24      inference('demod', [status(thm)], ['38', '41', '42'])).
% 1.02/1.24  thf('44', plain,
% 1.02/1.24      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.24         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.02/1.24         = (k3_xboole_0 @ sk_B @ sk_C))),
% 1.02/1.24      inference('sup-', [status(thm)], ['35', '43'])).
% 1.02/1.24  thf('45', plain,
% 1.02/1.24      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.02/1.24         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.24            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.24            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.02/1.24      inference('demod', [status(thm)], ['34', '44'])).
% 1.02/1.24  thf('46', plain,
% 1.02/1.24      ((v5_tops_1 @ 
% 1.02/1.24        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.02/1.24        sk_A)),
% 1.02/1.24      inference('demod', [status(thm)], ['29', '45'])).
% 1.02/1.24  thf('47', plain,
% 1.02/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf(t3_subset, axiom,
% 1.02/1.24    (![A:$i,B:$i]:
% 1.02/1.24     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.24  thf('48', plain,
% 1.02/1.24      (![X16 : $i, X17 : $i]:
% 1.02/1.24         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.02/1.24      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.24  thf('49', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.02/1.24      inference('sup-', [status(thm)], ['47', '48'])).
% 1.02/1.24  thf(t108_xboole_1, axiom,
% 1.02/1.24    (![A:$i,B:$i,C:$i]:
% 1.02/1.24     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 1.02/1.24  thf('50', plain,
% 1.02/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.24         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 1.02/1.24      inference('cnf', [status(esa)], [t108_xboole_1])).
% 1.02/1.24  thf('51', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.02/1.24      inference('sup-', [status(thm)], ['49', '50'])).
% 1.02/1.24  thf('52', plain,
% 1.02/1.24      (![X16 : $i, X18 : $i]:
% 1.02/1.24         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 1.02/1.24      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.24  thf('53', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 1.02/1.24          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.24      inference('sup-', [status(thm)], ['51', '52'])).
% 1.02/1.24  thf('54', plain,
% 1.02/1.24      (![X19 : $i, X20 : $i]:
% 1.02/1.24         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.02/1.24          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 1.02/1.24          | (v6_tops_1 @ X19 @ X20)
% 1.02/1.24          | ~ (l1_pre_topc @ X20))),
% 1.02/1.24      inference('cnf', [status(esa)], [t101_tops_1])).
% 1.02/1.24  thf('55', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         (~ (l1_pre_topc @ sk_A)
% 1.02/1.24          | (v6_tops_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.02/1.24          | ~ (v5_tops_1 @ 
% 1.02/1.24               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 1.02/1.24               sk_A))),
% 1.02/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.02/1.24  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.24  thf('57', plain,
% 1.02/1.24      (![X0 : $i]:
% 1.02/1.24         ((v6_tops_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.02/1.24          | ~ (v5_tops_1 @ 
% 1.02/1.24               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 1.02/1.24               sk_A))),
% 1.02/1.24      inference('demod', [status(thm)], ['55', '56'])).
% 1.02/1.24  thf('58', plain, ((v6_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 1.02/1.24      inference('sup-', [status(thm)], ['46', '57'])).
% 1.02/1.24  thf('59', plain, ($false), inference('demod', [status(thm)], ['4', '58'])).
% 1.02/1.24  
% 1.02/1.24  % SZS output end Refutation
% 1.02/1.24  
% 1.07/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
