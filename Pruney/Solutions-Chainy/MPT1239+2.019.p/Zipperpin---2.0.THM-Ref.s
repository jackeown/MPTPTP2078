%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1F3IAQis1e

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:03 EST 2020

% Result     : Theorem 8.30s
% Output     : Refutation 8.30s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 126 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  665 (1518 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k4_xboole_0 @ X11 @ X10 ) @ ( k4_xboole_0 @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['20','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1F3IAQis1e
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.30/8.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.30/8.49  % Solved by: fo/fo7.sh
% 8.30/8.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.30/8.49  % done 9677 iterations in 8.031s
% 8.30/8.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.30/8.49  % SZS output start Refutation
% 8.30/8.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.30/8.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.30/8.49  thf(sk_B_type, type, sk_B: $i).
% 8.30/8.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.30/8.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.30/8.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.30/8.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.30/8.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.30/8.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.30/8.49  thf(sk_C_type, type, sk_C: $i).
% 8.30/8.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.30/8.49  thf(sk_A_type, type, sk_A: $i).
% 8.30/8.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.30/8.49  thf(t50_tops_1, conjecture,
% 8.30/8.49    (![A:$i]:
% 8.30/8.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.30/8.49       ( ![B:$i]:
% 8.30/8.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.30/8.49           ( ![C:$i]:
% 8.30/8.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.30/8.49               ( r1_tarski @
% 8.30/8.49                 ( k1_tops_1 @
% 8.30/8.49                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.30/8.49                 ( k7_subset_1 @
% 8.30/8.49                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.30/8.49                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.30/8.49  thf(zf_stmt_0, negated_conjecture,
% 8.30/8.49    (~( ![A:$i]:
% 8.30/8.49        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.30/8.49          ( ![B:$i]:
% 8.30/8.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.30/8.49              ( ![C:$i]:
% 8.30/8.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.30/8.49                  ( r1_tarski @
% 8.30/8.49                    ( k1_tops_1 @
% 8.30/8.49                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.30/8.49                    ( k7_subset_1 @
% 8.30/8.49                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.30/8.49                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 8.30/8.49    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 8.30/8.49  thf('0', plain,
% 8.30/8.49      (~ (r1_tarski @ 
% 8.30/8.49          (k1_tops_1 @ sk_A @ 
% 8.30/8.49           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 8.30/8.49          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.30/8.49           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf('1', plain,
% 8.30/8.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf(redefinition_k7_subset_1, axiom,
% 8.30/8.49    (![A:$i,B:$i,C:$i]:
% 8.30/8.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.30/8.49       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.30/8.49  thf('2', plain,
% 8.30/8.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 8.30/8.49         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 8.30/8.49          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 8.30/8.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.30/8.49  thf('3', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.30/8.49           = (k4_xboole_0 @ sk_B @ X0))),
% 8.30/8.49      inference('sup-', [status(thm)], ['1', '2'])).
% 8.30/8.49  thf('4', plain,
% 8.30/8.49      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.30/8.49          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.30/8.49           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.30/8.49      inference('demod', [status(thm)], ['0', '3'])).
% 8.30/8.49  thf('5', plain,
% 8.30/8.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf(t3_subset, axiom,
% 8.30/8.49    (![A:$i,B:$i]:
% 8.30/8.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.30/8.49  thf('6', plain,
% 8.30/8.49      (![X23 : $i, X24 : $i]:
% 8.30/8.49         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 8.30/8.49      inference('cnf', [status(esa)], [t3_subset])).
% 8.30/8.49  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.30/8.49      inference('sup-', [status(thm)], ['5', '6'])).
% 8.30/8.49  thf('8', plain,
% 8.30/8.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf(t44_tops_1, axiom,
% 8.30/8.49    (![A:$i]:
% 8.30/8.49     ( ( l1_pre_topc @ A ) =>
% 8.30/8.49       ( ![B:$i]:
% 8.30/8.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.30/8.49           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 8.30/8.49  thf('9', plain,
% 8.30/8.49      (![X26 : $i, X27 : $i]:
% 8.30/8.49         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 8.30/8.49          | ~ (l1_pre_topc @ X27))),
% 8.30/8.49      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.30/8.49  thf('10', plain,
% 8.30/8.49      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 8.30/8.49      inference('sup-', [status(thm)], ['8', '9'])).
% 8.30/8.49  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 8.30/8.49      inference('demod', [status(thm)], ['10', '11'])).
% 8.30/8.49  thf(t1_xboole_1, axiom,
% 8.30/8.49    (![A:$i,B:$i,C:$i]:
% 8.30/8.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.30/8.49       ( r1_tarski @ A @ C ) ))).
% 8.30/8.49  thf('13', plain,
% 8.30/8.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.30/8.49         (~ (r1_tarski @ X6 @ X7)
% 8.30/8.49          | ~ (r1_tarski @ X7 @ X8)
% 8.30/8.49          | (r1_tarski @ X6 @ X8))),
% 8.30/8.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.30/8.49  thf('14', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 8.30/8.49          | ~ (r1_tarski @ sk_B @ X0))),
% 8.30/8.49      inference('sup-', [status(thm)], ['12', '13'])).
% 8.30/8.49  thf('15', plain,
% 8.30/8.49      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 8.30/8.49      inference('sup-', [status(thm)], ['7', '14'])).
% 8.30/8.49  thf('16', plain,
% 8.30/8.49      (![X23 : $i, X25 : $i]:
% 8.30/8.49         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 8.30/8.49      inference('cnf', [status(esa)], [t3_subset])).
% 8.30/8.49  thf('17', plain,
% 8.30/8.49      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.30/8.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('sup-', [status(thm)], ['15', '16'])).
% 8.30/8.49  thf('18', plain,
% 8.30/8.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 8.30/8.49         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 8.30/8.49          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 8.30/8.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.30/8.49  thf('19', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 8.30/8.49           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 8.30/8.49      inference('sup-', [status(thm)], ['17', '18'])).
% 8.30/8.49  thf('20', plain,
% 8.30/8.49      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.30/8.49          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.30/8.49      inference('demod', [status(thm)], ['4', '19'])).
% 8.30/8.49  thf('21', plain,
% 8.30/8.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf('22', plain,
% 8.30/8.49      (![X26 : $i, X27 : $i]:
% 8.30/8.49         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 8.30/8.49          | ~ (l1_pre_topc @ X27))),
% 8.30/8.49      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.30/8.49  thf('23', plain,
% 8.30/8.49      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 8.30/8.49      inference('sup-', [status(thm)], ['21', '22'])).
% 8.30/8.49  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf('25', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 8.30/8.49      inference('demod', [status(thm)], ['23', '24'])).
% 8.30/8.49  thf(t34_xboole_1, axiom,
% 8.30/8.49    (![A:$i,B:$i,C:$i]:
% 8.30/8.49     ( ( r1_tarski @ A @ B ) =>
% 8.30/8.49       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 8.30/8.49  thf('26', plain,
% 8.30/8.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 8.30/8.49         (~ (r1_tarski @ X9 @ X10)
% 8.30/8.49          | (r1_tarski @ (k4_xboole_0 @ X11 @ X10) @ (k4_xboole_0 @ X11 @ X9)))),
% 8.30/8.49      inference('cnf', [status(esa)], [t34_xboole_1])).
% 8.30/8.49  thf('27', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 8.30/8.49          (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.30/8.49      inference('sup-', [status(thm)], ['25', '26'])).
% 8.30/8.49  thf('28', plain,
% 8.30/8.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf('29', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.30/8.49      inference('sup-', [status(thm)], ['5', '6'])).
% 8.30/8.49  thf(t36_xboole_1, axiom,
% 8.30/8.49    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.30/8.49  thf('30', plain,
% 8.30/8.49      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 8.30/8.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.30/8.49  thf('31', plain,
% 8.30/8.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.30/8.49         (~ (r1_tarski @ X6 @ X7)
% 8.30/8.49          | ~ (r1_tarski @ X7 @ X8)
% 8.30/8.49          | (r1_tarski @ X6 @ X8))),
% 8.30/8.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.30/8.49  thf('32', plain,
% 8.30/8.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.30/8.49         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 8.30/8.49      inference('sup-', [status(thm)], ['30', '31'])).
% 8.30/8.49  thf('33', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 8.30/8.49      inference('sup-', [status(thm)], ['29', '32'])).
% 8.30/8.49  thf('34', plain,
% 8.30/8.49      (![X23 : $i, X25 : $i]:
% 8.30/8.49         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 8.30/8.49      inference('cnf', [status(esa)], [t3_subset])).
% 8.30/8.49  thf('35', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.30/8.49          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('sup-', [status(thm)], ['33', '34'])).
% 8.30/8.49  thf(t48_tops_1, axiom,
% 8.30/8.49    (![A:$i]:
% 8.30/8.49     ( ( l1_pre_topc @ A ) =>
% 8.30/8.49       ( ![B:$i]:
% 8.30/8.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.30/8.49           ( ![C:$i]:
% 8.30/8.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.30/8.49               ( ( r1_tarski @ B @ C ) =>
% 8.30/8.49                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.30/8.49  thf('36', plain,
% 8.30/8.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.30/8.49         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 8.30/8.49          | ~ (r1_tarski @ X28 @ X30)
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 8.30/8.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 8.30/8.49          | ~ (l1_pre_topc @ X29))),
% 8.30/8.49      inference('cnf', [status(esa)], [t48_tops_1])).
% 8.30/8.49  thf('37', plain,
% 8.30/8.49      (![X0 : $i, X1 : $i]:
% 8.30/8.49         (~ (l1_pre_topc @ sk_A)
% 8.30/8.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49             (k1_tops_1 @ sk_A @ X1))
% 8.30/8.49          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.30/8.49      inference('sup-', [status(thm)], ['35', '36'])).
% 8.30/8.49  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf('39', plain,
% 8.30/8.49      (![X0 : $i, X1 : $i]:
% 8.30/8.49         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49             (k1_tops_1 @ sk_A @ X1))
% 8.30/8.49          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.30/8.49      inference('demod', [status(thm)], ['37', '38'])).
% 8.30/8.49  thf('40', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49             (k1_tops_1 @ sk_A @ sk_B)))),
% 8.30/8.49      inference('sup-', [status(thm)], ['28', '39'])).
% 8.30/8.49  thf('41', plain,
% 8.30/8.49      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 8.30/8.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.30/8.49  thf('42', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49          (k1_tops_1 @ sk_A @ sk_B))),
% 8.30/8.49      inference('demod', [status(thm)], ['40', '41'])).
% 8.30/8.49  thf('43', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.30/8.49          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.30/8.49      inference('sup-', [status(thm)], ['33', '34'])).
% 8.30/8.49  thf('44', plain,
% 8.30/8.49      (![X26 : $i, X27 : $i]:
% 8.30/8.49         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 8.30/8.49          | ~ (l1_pre_topc @ X27))),
% 8.30/8.49      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.30/8.49  thf('45', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (~ (l1_pre_topc @ sk_A)
% 8.30/8.49          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49             (k4_xboole_0 @ sk_B @ X0)))),
% 8.30/8.49      inference('sup-', [status(thm)], ['43', '44'])).
% 8.30/8.49  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 8.30/8.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.30/8.49  thf('47', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49          (k4_xboole_0 @ sk_B @ X0))),
% 8.30/8.49      inference('demod', [status(thm)], ['45', '46'])).
% 8.30/8.49  thf(t106_xboole_1, axiom,
% 8.30/8.49    (![A:$i,B:$i,C:$i]:
% 8.30/8.49     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 8.30/8.49       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 8.30/8.49  thf('48', plain,
% 8.30/8.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.30/8.49         ((r1_xboole_0 @ X3 @ X5)
% 8.30/8.49          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 8.30/8.49      inference('cnf', [status(esa)], [t106_xboole_1])).
% 8.30/8.49  thf('49', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 8.30/8.49      inference('sup-', [status(thm)], ['47', '48'])).
% 8.30/8.49  thf(t86_xboole_1, axiom,
% 8.30/8.49    (![A:$i,B:$i,C:$i]:
% 8.30/8.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 8.30/8.49       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 8.30/8.49  thf('50', plain,
% 8.30/8.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.30/8.49         (~ (r1_tarski @ X17 @ X18)
% 8.30/8.49          | ~ (r1_xboole_0 @ X17 @ X19)
% 8.30/8.49          | (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 8.30/8.49      inference('cnf', [status(esa)], [t86_xboole_1])).
% 8.30/8.49  thf('51', plain,
% 8.30/8.49      (![X0 : $i, X1 : $i]:
% 8.30/8.49         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49           (k4_xboole_0 @ X1 @ X0))
% 8.30/8.49          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1))),
% 8.30/8.49      inference('sup-', [status(thm)], ['49', '50'])).
% 8.30/8.49  thf('52', plain,
% 8.30/8.49      (![X0 : $i]:
% 8.30/8.49         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.30/8.49          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 8.30/8.49      inference('sup-', [status(thm)], ['42', '51'])).
% 8.30/8.49  thf('53', plain,
% 8.30/8.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.30/8.49         (~ (r1_tarski @ X6 @ X7)
% 8.30/8.49          | ~ (r1_tarski @ X7 @ X8)
% 8.30/8.49          | (r1_tarski @ X6 @ X8))),
% 8.30/8.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.30/8.49  thf('54', plain,
% 8.30/8.49      (![X0 : $i, X1 : $i]:
% 8.30/8.49         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1)
% 8.30/8.49          | ~ (r1_tarski @ (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ X1))),
% 8.30/8.49      inference('sup-', [status(thm)], ['52', '53'])).
% 8.30/8.49  thf('55', plain,
% 8.30/8.49      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.30/8.49        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.30/8.49      inference('sup-', [status(thm)], ['27', '54'])).
% 8.30/8.49  thf('56', plain, ($false), inference('demod', [status(thm)], ['20', '55'])).
% 8.30/8.49  
% 8.30/8.49  % SZS output end Refutation
% 8.30/8.49  
% 8.30/8.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
