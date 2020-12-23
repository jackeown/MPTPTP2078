%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cPt4w2TaTW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:57 EST 2020

% Result     : Theorem 11.45s
% Output     : Refutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 202 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  982 (2620 expanded)
%              Number of equality atoms :   34 (  55 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
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

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v5_tops_1 @ X28 @ X29 )
      | ~ ( v5_tops_1 @ X30 @ X29 )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t108_tops_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X2 ) @ X0 )
      | ~ ( v5_tops_1 @ X2 @ X0 )
      | ~ ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t101_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v6_tops_1 @ X26 @ X27 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ( v5_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v5_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','48'])).

thf('50',plain,
    ( ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v6_tops_1 @ X26 @ X27 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v6_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['50','56','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ( v6_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v6_tops_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v6_tops_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    v6_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['4','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cPt4w2TaTW
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 11.45/11.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.45/11.66  % Solved by: fo/fo7.sh
% 11.45/11.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.45/11.66  % done 8060 iterations in 11.199s
% 11.45/11.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.45/11.66  % SZS output start Refutation
% 11.45/11.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.45/11.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.45/11.66  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 11.45/11.66  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 11.45/11.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 11.45/11.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.45/11.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 11.45/11.66  thf(sk_C_type, type, sk_C: $i).
% 11.45/11.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 11.45/11.66  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 11.45/11.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 11.45/11.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.45/11.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.45/11.66  thf(sk_A_type, type, sk_A: $i).
% 11.45/11.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.45/11.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.45/11.66  thf(sk_B_type, type, sk_B: $i).
% 11.45/11.66  thf(t109_tops_1, conjecture,
% 11.45/11.66    (![A:$i]:
% 11.45/11.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.45/11.66       ( ![B:$i]:
% 11.45/11.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.45/11.66           ( ![C:$i]:
% 11.45/11.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.45/11.66               ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 11.45/11.66                 ( v6_tops_1 @
% 11.45/11.66                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 11.45/11.66  thf(zf_stmt_0, negated_conjecture,
% 11.45/11.66    (~( ![A:$i]:
% 11.45/11.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.45/11.66          ( ![B:$i]:
% 11.45/11.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.45/11.66              ( ![C:$i]:
% 11.45/11.66                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.45/11.66                  ( ( ( v6_tops_1 @ B @ A ) & ( v6_tops_1 @ C @ A ) ) =>
% 11.45/11.66                    ( v6_tops_1 @
% 11.45/11.66                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 11.45/11.66    inference('cnf.neg', [status(esa)], [t109_tops_1])).
% 11.45/11.66  thf('0', plain,
% 11.45/11.66      (~ (v6_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('1', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf(redefinition_k9_subset_1, axiom,
% 11.45/11.66    (![A:$i,B:$i,C:$i]:
% 11.45/11.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 11.45/11.66       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 11.45/11.66  thf('2', plain,
% 11.45/11.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.45/11.66         (((k9_subset_1 @ X22 @ X20 @ X21) = (k3_xboole_0 @ X20 @ X21))
% 11.45/11.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 11.45/11.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 11.45/11.66  thf('3', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 11.45/11.66           = (k3_xboole_0 @ X0 @ sk_C))),
% 11.45/11.66      inference('sup-', [status(thm)], ['1', '2'])).
% 11.45/11.66  thf('4', plain, (~ (v6_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 11.45/11.66      inference('demod', [status(thm)], ['0', '3'])).
% 11.45/11.66  thf('5', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf(d5_subset_1, axiom,
% 11.45/11.66    (![A:$i,B:$i]:
% 11.45/11.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.45/11.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 11.45/11.66  thf('6', plain,
% 11.45/11.66      (![X12 : $i, X13 : $i]:
% 11.45/11.66         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 11.45/11.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 11.45/11.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.45/11.66  thf('7', plain,
% 11.45/11.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 11.45/11.66         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 11.45/11.66      inference('sup-', [status(thm)], ['5', '6'])).
% 11.45/11.66  thf('8', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('9', plain,
% 11.45/11.66      (![X12 : $i, X13 : $i]:
% 11.45/11.66         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 11.45/11.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 11.45/11.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.45/11.66  thf('10', plain,
% 11.45/11.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.45/11.66         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.45/11.66      inference('sup-', [status(thm)], ['8', '9'])).
% 11.45/11.66  thf(t36_xboole_1, axiom,
% 11.45/11.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 11.45/11.66  thf('11', plain,
% 11.45/11.66      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 11.45/11.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.45/11.66  thf('12', plain,
% 11.45/11.66      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 11.45/11.66        (u1_struct_0 @ sk_A))),
% 11.45/11.66      inference('sup+', [status(thm)], ['10', '11'])).
% 11.45/11.66  thf(t3_subset, axiom,
% 11.45/11.66    (![A:$i,B:$i]:
% 11.45/11.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.45/11.66  thf('13', plain,
% 11.45/11.66      (![X23 : $i, X25 : $i]:
% 11.45/11.66         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 11.45/11.66      inference('cnf', [status(esa)], [t3_subset])).
% 11.45/11.66  thf('14', plain,
% 11.45/11.66      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 11.45/11.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['12', '13'])).
% 11.45/11.66  thf('15', plain,
% 11.45/11.66      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 11.45/11.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.45/11.66  thf('16', plain,
% 11.45/11.66      (![X23 : $i, X25 : $i]:
% 11.45/11.66         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 11.45/11.66      inference('cnf', [status(esa)], [t3_subset])).
% 11.45/11.66  thf('17', plain,
% 11.45/11.66      (![X0 : $i, X1 : $i]:
% 11.45/11.66         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 11.45/11.66      inference('sup-', [status(thm)], ['15', '16'])).
% 11.45/11.66  thf(t108_tops_1, axiom,
% 11.45/11.66    (![A:$i]:
% 11.45/11.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.45/11.66       ( ![B:$i]:
% 11.45/11.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.45/11.66           ( ![C:$i]:
% 11.45/11.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.45/11.66               ( ( ( v5_tops_1 @ B @ A ) & ( v5_tops_1 @ C @ A ) ) =>
% 11.45/11.66                 ( v5_tops_1 @
% 11.45/11.66                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 11.45/11.66  thf('18', plain,
% 11.45/11.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 11.45/11.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 11.45/11.66          | ~ (v5_tops_1 @ X28 @ X29)
% 11.45/11.66          | ~ (v5_tops_1 @ X30 @ X29)
% 11.45/11.66          | (v5_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ X29) @ X28 @ X30) @ X29)
% 11.45/11.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 11.45/11.66          | ~ (l1_pre_topc @ X29)
% 11.45/11.66          | ~ (v2_pre_topc @ X29))),
% 11.45/11.66      inference('cnf', [status(esa)], [t108_tops_1])).
% 11.45/11.66  thf('19', plain,
% 11.45/11.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.45/11.66         (~ (v2_pre_topc @ X0)
% 11.45/11.66          | ~ (l1_pre_topc @ X0)
% 11.45/11.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 11.45/11.66          | (v5_tops_1 @ 
% 11.45/11.66             (k4_subset_1 @ (u1_struct_0 @ X0) @ 
% 11.45/11.66              (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X2) @ 
% 11.45/11.66             X0)
% 11.45/11.66          | ~ (v5_tops_1 @ X2 @ X0)
% 11.45/11.66          | ~ (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 11.45/11.66      inference('sup-', [status(thm)], ['17', '18'])).
% 11.45/11.66  thf('20', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (~ (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_A)
% 11.45/11.66          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 11.45/11.66          | (v5_tops_1 @ 
% 11.45/11.66             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.45/11.66              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.45/11.66              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 11.45/11.66             sk_A)
% 11.45/11.66          | ~ (l1_pre_topc @ sk_A)
% 11.45/11.66          | ~ (v2_pre_topc @ sk_A))),
% 11.45/11.66      inference('sup-', [status(thm)], ['14', '19'])).
% 11.45/11.66  thf('21', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf(t101_tops_1, axiom,
% 11.45/11.66    (![A:$i]:
% 11.45/11.66     ( ( l1_pre_topc @ A ) =>
% 11.45/11.66       ( ![B:$i]:
% 11.45/11.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.45/11.66           ( ( v6_tops_1 @ B @ A ) <=>
% 11.45/11.66             ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 11.45/11.66  thf('22', plain,
% 11.45/11.66      (![X26 : $i, X27 : $i]:
% 11.45/11.66         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 11.45/11.66          | ~ (v6_tops_1 @ X26 @ X27)
% 11.45/11.66          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 11.45/11.66          | ~ (l1_pre_topc @ X27))),
% 11.45/11.66      inference('cnf', [status(esa)], [t101_tops_1])).
% 11.45/11.66  thf('23', plain,
% 11.45/11.66      ((~ (l1_pre_topc @ sk_A)
% 11.45/11.66        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 11.45/11.66        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 11.45/11.66      inference('sup-', [status(thm)], ['21', '22'])).
% 11.45/11.66  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('25', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('26', plain,
% 11.45/11.66      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 11.45/11.66      inference('demod', [status(thm)], ['23', '24', '25'])).
% 11.45/11.66  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('29', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (~ (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_A)
% 11.45/11.66          | (v5_tops_1 @ 
% 11.45/11.66             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.45/11.66              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.45/11.66              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 11.45/11.66             sk_A))),
% 11.45/11.66      inference('demod', [status(thm)], ['20', '26', '27', '28'])).
% 11.45/11.66  thf('30', plain,
% 11.45/11.66      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 11.45/11.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['12', '13'])).
% 11.45/11.66  thf('31', plain,
% 11.45/11.66      (![X0 : $i, X1 : $i]:
% 11.45/11.66         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 11.45/11.66      inference('sup-', [status(thm)], ['15', '16'])).
% 11.45/11.66  thf(redefinition_k4_subset_1, axiom,
% 11.45/11.66    (![A:$i,B:$i,C:$i]:
% 11.45/11.66     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 11.45/11.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 11.45/11.66       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 11.45/11.66  thf('32', plain,
% 11.45/11.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 11.45/11.66         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 11.45/11.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 11.45/11.66          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 11.45/11.66      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 11.45/11.66  thf('33', plain,
% 11.45/11.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.45/11.66         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 11.45/11.66            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 11.45/11.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['31', '32'])).
% 11.45/11.66  thf('34', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.45/11.66           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.45/11.66           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.45/11.66           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.45/11.66              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['30', '33'])).
% 11.45/11.66  thf('35', plain,
% 11.45/11.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.45/11.66         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.45/11.66      inference('sup-', [status(thm)], ['8', '9'])).
% 11.45/11.66  thf(l36_xboole_1, axiom,
% 11.45/11.66    (![A:$i,B:$i,C:$i]:
% 11.45/11.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 11.45/11.66       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 11.45/11.66  thf('36', plain,
% 11.45/11.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.45/11.66         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7))
% 11.45/11.66           = (k2_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X7)))),
% 11.45/11.66      inference('cnf', [status(esa)], [l36_xboole_1])).
% 11.45/11.66  thf('37', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 11.45/11.66           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.45/11.66              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 11.45/11.66      inference('sup+', [status(thm)], ['35', '36'])).
% 11.45/11.66  thf('38', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf(dt_k9_subset_1, axiom,
% 11.45/11.66    (![A:$i,B:$i,C:$i]:
% 11.45/11.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 11.45/11.66       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 11.45/11.66  thf('39', plain,
% 11.45/11.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 11.45/11.66         ((m1_subset_1 @ (k9_subset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 11.45/11.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X14)))),
% 11.45/11.66      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 11.45/11.66  thf('40', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 11.45/11.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['38', '39'])).
% 11.45/11.66  thf('41', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('42', plain,
% 11.45/11.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 11.45/11.66         (((k9_subset_1 @ X22 @ X20 @ X21) = (k3_xboole_0 @ X20 @ X21))
% 11.45/11.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 11.45/11.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 11.45/11.66  thf('43', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 11.45/11.66           = (k3_xboole_0 @ X0 @ sk_B))),
% 11.45/11.66      inference('sup-', [status(thm)], ['41', '42'])).
% 11.45/11.66  thf('44', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 11.45/11.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('demod', [status(thm)], ['40', '43'])).
% 11.45/11.66  thf('45', plain,
% 11.45/11.66      (![X12 : $i, X13 : $i]:
% 11.45/11.66         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 11.45/11.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 11.45/11.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.45/11.66  thf('46', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 11.45/11.66           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['44', '45'])).
% 11.45/11.66  thf('47', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 11.45/11.66           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.45/11.66              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 11.45/11.66      inference('demod', [status(thm)], ['37', '46'])).
% 11.45/11.66  thf('48', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.45/11.66           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.45/11.66           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.45/11.66           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B)))),
% 11.45/11.66      inference('demod', [status(thm)], ['34', '47'])).
% 11.45/11.66  thf('49', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (~ (v5_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_A)
% 11.45/11.66          | (v5_tops_1 @ 
% 11.45/11.66             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 11.45/11.66             sk_A))),
% 11.45/11.66      inference('demod', [status(thm)], ['29', '48'])).
% 11.45/11.66  thf('50', plain,
% 11.45/11.66      ((~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 11.45/11.66        | (v5_tops_1 @ 
% 11.45/11.66           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_C @ sk_B)) @ 
% 11.45/11.66           sk_A))),
% 11.45/11.66      inference('sup-', [status(thm)], ['7', '49'])).
% 11.45/11.66  thf('51', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('52', plain,
% 11.45/11.66      (![X26 : $i, X27 : $i]:
% 11.45/11.66         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 11.45/11.66          | ~ (v6_tops_1 @ X26 @ X27)
% 11.45/11.66          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 11.45/11.66          | ~ (l1_pre_topc @ X27))),
% 11.45/11.66      inference('cnf', [status(esa)], [t101_tops_1])).
% 11.45/11.66  thf('53', plain,
% 11.45/11.66      ((~ (l1_pre_topc @ sk_A)
% 11.45/11.66        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 11.45/11.66        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 11.45/11.66      inference('sup-', [status(thm)], ['51', '52'])).
% 11.45/11.66  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('55', plain, ((v6_tops_1 @ sk_C @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('56', plain,
% 11.45/11.66      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 11.45/11.66      inference('demod', [status(thm)], ['53', '54', '55'])).
% 11.45/11.66  thf('57', plain,
% 11.45/11.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.45/11.66         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7))
% 11.45/11.66           = (k2_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X7)))),
% 11.45/11.66      inference('cnf', [status(esa)], [l36_xboole_1])).
% 11.45/11.66  thf(commutativity_k2_xboole_0, axiom,
% 11.45/11.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 11.45/11.66  thf('58', plain,
% 11.45/11.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.45/11.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.45/11.66  thf('59', plain,
% 11.45/11.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.45/11.66         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 11.45/11.66           = (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.45/11.66      inference('sup+', [status(thm)], ['57', '58'])).
% 11.45/11.66  thf('60', plain,
% 11.45/11.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.45/11.66         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7))
% 11.45/11.66           = (k2_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X7)))),
% 11.45/11.66      inference('cnf', [status(esa)], [l36_xboole_1])).
% 11.45/11.66  thf('61', plain,
% 11.45/11.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.45/11.66         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 11.45/11.66           = (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.45/11.66      inference('sup+', [status(thm)], ['59', '60'])).
% 11.45/11.66  thf('62', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 11.45/11.66           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['44', '45'])).
% 11.45/11.66  thf('63', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 11.45/11.66           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))),
% 11.45/11.66      inference('sup+', [status(thm)], ['61', '62'])).
% 11.45/11.66  thf('64', plain,
% 11.45/11.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('65', plain,
% 11.45/11.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 11.45/11.66         ((m1_subset_1 @ (k9_subset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 11.45/11.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X14)))),
% 11.45/11.66      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 11.45/11.66  thf('66', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 11.45/11.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['64', '65'])).
% 11.45/11.66  thf('67', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 11.45/11.66           = (k3_xboole_0 @ X0 @ sk_C))),
% 11.45/11.66      inference('sup-', [status(thm)], ['1', '2'])).
% 11.45/11.66  thf('68', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 11.45/11.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('demod', [status(thm)], ['66', '67'])).
% 11.45/11.66  thf('69', plain,
% 11.45/11.66      (![X12 : $i, X13 : $i]:
% 11.45/11.66         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 11.45/11.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 11.45/11.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.45/11.66  thf('70', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C))
% 11.45/11.66           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C)))),
% 11.45/11.66      inference('sup-', [status(thm)], ['68', '69'])).
% 11.45/11.66  thf('71', plain,
% 11.45/11.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C))
% 11.45/11.66         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 11.45/11.66      inference('sup+', [status(thm)], ['63', '70'])).
% 11.45/11.66  thf('72', plain,
% 11.45/11.66      ((v5_tops_1 @ 
% 11.45/11.66        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 11.45/11.66        sk_A)),
% 11.45/11.66      inference('demod', [status(thm)], ['50', '56', '71'])).
% 11.45/11.66  thf('73', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 11.45/11.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.45/11.66      inference('demod', [status(thm)], ['66', '67'])).
% 11.45/11.66  thf('74', plain,
% 11.45/11.66      (![X26 : $i, X27 : $i]:
% 11.45/11.66         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 11.45/11.66          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 11.45/11.66          | (v6_tops_1 @ X26 @ X27)
% 11.45/11.66          | ~ (l1_pre_topc @ X27))),
% 11.45/11.66      inference('cnf', [status(esa)], [t101_tops_1])).
% 11.45/11.66  thf('75', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         (~ (l1_pre_topc @ sk_A)
% 11.45/11.66          | (v6_tops_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 11.45/11.66          | ~ (v5_tops_1 @ 
% 11.45/11.66               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 11.45/11.66               sk_A))),
% 11.45/11.66      inference('sup-', [status(thm)], ['73', '74'])).
% 11.45/11.66  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 11.45/11.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.45/11.66  thf('77', plain,
% 11.45/11.66      (![X0 : $i]:
% 11.45/11.66         ((v6_tops_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 11.45/11.66          | ~ (v5_tops_1 @ 
% 11.45/11.66               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 11.45/11.66               sk_A))),
% 11.45/11.66      inference('demod', [status(thm)], ['75', '76'])).
% 11.45/11.66  thf('78', plain, ((v6_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 11.45/11.66      inference('sup-', [status(thm)], ['72', '77'])).
% 11.45/11.66  thf('79', plain, ($false), inference('demod', [status(thm)], ['4', '78'])).
% 11.45/11.66  
% 11.45/11.66  % SZS output end Refutation
% 11.45/11.66  
% 11.45/11.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
