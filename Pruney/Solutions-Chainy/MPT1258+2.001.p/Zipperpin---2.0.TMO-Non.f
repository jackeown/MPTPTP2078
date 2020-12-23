%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.avF6kNjyl8

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:19 EST 2020

% Result     : Timeout 59.04s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  143 ( 257 expanded)
%              Number of leaves         :   39 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          : 1371 (3021 expanded)
%              Number of equality atoms :   63 ( 136 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t74_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k1_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X47 @ X46 ) @ X46 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X49 @ X48 ) @ ( k2_tops_1 @ X49 @ X48 ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( ( k4_xboole_0 @ X4 @ X3 )
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
       != ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0
     != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    k1_xboole_0
 != ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( r1_tarski @ X36 @ ( k2_pre_topc @ X37 @ X36 ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('35',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('46',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X33 @ X31 )
        = ( k9_subset_1 @ X32 @ X33 @ ( k3_subset_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_tops_1 @ X41 @ X40 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k2_pre_topc @ X41 @ X40 ) @ ( k2_pre_topc @ X41 @ ( k3_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 ) ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('60',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('65',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('66',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ X38 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ ( k3_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 ) ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','72'])).

thf('74',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','73'])).

thf('75',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('78',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('82',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('86',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('87',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('91',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('92',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_subset_1 @ X17 @ X18 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','95'])).

thf('97',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','96'])).

thf('98',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('99',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['24','97','100'])).

thf('102',plain,(
    $false ),
    inference(simplify,[status(thm)],['101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.avF6kNjyl8
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 59.04/59.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 59.04/59.24  % Solved by: fo/fo7.sh
% 59.04/59.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.04/59.24  % done 6239 iterations in 58.791s
% 59.04/59.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 59.04/59.24  % SZS output start Refutation
% 59.04/59.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 59.04/59.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 59.04/59.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 59.04/59.24  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 59.04/59.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 59.04/59.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 59.04/59.24  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 59.04/59.24  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 59.04/59.24  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 59.04/59.24  thf(sk_B_type, type, sk_B: $i).
% 59.04/59.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 59.04/59.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 59.04/59.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 59.04/59.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 59.04/59.25  thf(sk_A_type, type, sk_A: $i).
% 59.04/59.25  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 59.04/59.25  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 59.04/59.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 59.04/59.25  thf(t74_tops_1, conjecture,
% 59.04/59.25    (![A:$i]:
% 59.04/59.25     ( ( l1_pre_topc @ A ) =>
% 59.04/59.25       ( ![B:$i]:
% 59.04/59.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.04/59.25           ( ( k1_tops_1 @ A @ B ) =
% 59.04/59.25             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 59.04/59.25  thf(zf_stmt_0, negated_conjecture,
% 59.04/59.25    (~( ![A:$i]:
% 59.04/59.25        ( ( l1_pre_topc @ A ) =>
% 59.04/59.25          ( ![B:$i]:
% 59.04/59.25            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.04/59.25              ( ( k1_tops_1 @ A @ B ) =
% 59.04/59.25                ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 59.04/59.25    inference('cnf.neg', [status(esa)], [t74_tops_1])).
% 59.04/59.25  thf('0', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(t44_tops_1, axiom,
% 59.04/59.25    (![A:$i]:
% 59.04/59.25     ( ( l1_pre_topc @ A ) =>
% 59.04/59.25       ( ![B:$i]:
% 59.04/59.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.04/59.25           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 59.04/59.25  thf('1', plain,
% 59.04/59.25      (![X46 : $i, X47 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 59.04/59.25          | (r1_tarski @ (k1_tops_1 @ X47 @ X46) @ X46)
% 59.04/59.25          | ~ (l1_pre_topc @ X47))),
% 59.04/59.25      inference('cnf', [status(esa)], [t44_tops_1])).
% 59.04/59.25  thf('2', plain,
% 59.04/59.25      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 59.04/59.25      inference('sup-', [status(thm)], ['0', '1'])).
% 59.04/59.25  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('4', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 59.04/59.25      inference('demod', [status(thm)], ['2', '3'])).
% 59.04/59.25  thf('5', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(t73_tops_1, axiom,
% 59.04/59.25    (![A:$i]:
% 59.04/59.25     ( ( l1_pre_topc @ A ) =>
% 59.04/59.25       ( ![B:$i]:
% 59.04/59.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.04/59.25           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 59.04/59.25  thf('6', plain,
% 59.04/59.25      (![X48 : $i, X49 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 59.04/59.25          | (r1_xboole_0 @ (k1_tops_1 @ X49 @ X48) @ (k2_tops_1 @ X49 @ X48))
% 59.04/59.25          | ~ (l1_pre_topc @ X49))),
% 59.04/59.25      inference('cnf', [status(esa)], [t73_tops_1])).
% 59.04/59.25  thf('7', plain,
% 59.04/59.25      ((~ (l1_pre_topc @ sk_A)
% 59.04/59.25        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['5', '6'])).
% 59.04/59.25  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('9', plain,
% 59.04/59.25      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 59.04/59.25      inference('demod', [status(thm)], ['7', '8'])).
% 59.04/59.25  thf(t86_xboole_1, axiom,
% 59.04/59.25    (![A:$i,B:$i,C:$i]:
% 59.04/59.25     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 59.04/59.25       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 59.04/59.25  thf('10', plain,
% 59.04/59.25      (![X13 : $i, X14 : $i, X15 : $i]:
% 59.04/59.25         (~ (r1_tarski @ X13 @ X14)
% 59.04/59.25          | ~ (r1_xboole_0 @ X13 @ X15)
% 59.04/59.25          | (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 59.04/59.25      inference('cnf', [status(esa)], [t86_xboole_1])).
% 59.04/59.25  thf('11', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25           (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 59.04/59.25          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 59.04/59.25      inference('sup-', [status(thm)], ['9', '10'])).
% 59.04/59.25  thf('12', plain,
% 59.04/59.25      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['4', '11'])).
% 59.04/59.25  thf(t37_xboole_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 59.04/59.25  thf('13', plain,
% 59.04/59.25      (![X5 : $i, X7 : $i]:
% 59.04/59.25         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 59.04/59.25      inference('cnf', [status(esa)], [t37_xboole_1])).
% 59.04/59.25  thf('14', plain,
% 59.04/59.25      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25         (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (k1_xboole_0))),
% 59.04/59.25      inference('sup-', [status(thm)], ['12', '13'])).
% 59.04/59.25  thf(t41_xboole_1, axiom,
% 59.04/59.25    (![A:$i,B:$i,C:$i]:
% 59.04/59.25     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 59.04/59.25       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 59.04/59.25  thf('15', plain,
% 59.04/59.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 59.04/59.25         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 59.04/59.25           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 59.04/59.25      inference('cnf', [status(esa)], [t41_xboole_1])).
% 59.04/59.25  thf(t32_xboole_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 59.04/59.25       ( ( A ) = ( B ) ) ))).
% 59.04/59.25  thf('16', plain,
% 59.04/59.25      (![X3 : $i, X4 : $i]:
% 59.04/59.25         (((X4) = (X3)) | ((k4_xboole_0 @ X4 @ X3) != (k4_xboole_0 @ X3 @ X4)))),
% 59.04/59.25      inference('cnf', [status(esa)], [t32_xboole_1])).
% 59.04/59.25  thf('17', plain,
% 59.04/59.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.04/59.25         (((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 59.04/59.25            != (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 59.04/59.25          | ((X0) = (k4_xboole_0 @ X2 @ X1)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['15', '16'])).
% 59.04/59.25  thf('18', plain,
% 59.04/59.25      ((((k1_xboole_0)
% 59.04/59.25          != (k4_xboole_0 @ sk_B @ 
% 59.04/59.25              (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25               (k1_tops_1 @ sk_A @ sk_B))))
% 59.04/59.25        | ((k1_tops_1 @ sk_A @ sk_B)
% 59.04/59.25            = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['14', '17'])).
% 59.04/59.25  thf('19', plain,
% 59.04/59.25      (((k1_tops_1 @ sk_A @ sk_B)
% 59.04/59.25         != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 59.04/59.25             (k2_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('20', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(redefinition_k7_subset_1, axiom,
% 59.04/59.25    (![A:$i,B:$i,C:$i]:
% 59.04/59.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 59.04/59.25       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 59.04/59.25  thf('21', plain,
% 59.04/59.25      (![X28 : $i, X29 : $i, X30 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 59.04/59.25          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 59.04/59.25      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 59.04/59.25  thf('22', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 59.04/59.25           = (k4_xboole_0 @ sk_B @ X0))),
% 59.04/59.25      inference('sup-', [status(thm)], ['20', '21'])).
% 59.04/59.25  thf('23', plain,
% 59.04/59.25      (((k1_tops_1 @ sk_A @ sk_B)
% 59.04/59.25         != (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('demod', [status(thm)], ['19', '22'])).
% 59.04/59.25  thf('24', plain,
% 59.04/59.25      (((k1_xboole_0)
% 59.04/59.25         != (k4_xboole_0 @ sk_B @ 
% 59.04/59.25             (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25              (k1_tops_1 @ sk_A @ sk_B))))),
% 59.04/59.25      inference('simplify_reflect-', [status(thm)], ['18', '23'])).
% 59.04/59.25  thf('25', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(t48_pre_topc, axiom,
% 59.04/59.25    (![A:$i]:
% 59.04/59.25     ( ( l1_pre_topc @ A ) =>
% 59.04/59.25       ( ![B:$i]:
% 59.04/59.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.04/59.25           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 59.04/59.25  thf('26', plain,
% 59.04/59.25      (![X36 : $i, X37 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 59.04/59.25          | (r1_tarski @ X36 @ (k2_pre_topc @ X37 @ X36))
% 59.04/59.25          | ~ (l1_pre_topc @ X37))),
% 59.04/59.25      inference('cnf', [status(esa)], [t48_pre_topc])).
% 59.04/59.25  thf('27', plain,
% 59.04/59.25      ((~ (l1_pre_topc @ sk_A)
% 59.04/59.25        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['25', '26'])).
% 59.04/59.25  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('29', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 59.04/59.25      inference('demod', [status(thm)], ['27', '28'])).
% 59.04/59.25  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 59.04/59.25      inference('demod', [status(thm)], ['2', '3'])).
% 59.04/59.25  thf(t1_xboole_1, axiom,
% 59.04/59.25    (![A:$i,B:$i,C:$i]:
% 59.04/59.25     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 59.04/59.25       ( r1_tarski @ A @ C ) ))).
% 59.04/59.25  thf('31', plain,
% 59.04/59.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.04/59.25         (~ (r1_tarski @ X0 @ X1)
% 59.04/59.25          | ~ (r1_tarski @ X1 @ X2)
% 59.04/59.25          | (r1_tarski @ X0 @ X2))),
% 59.04/59.25      inference('cnf', [status(esa)], [t1_xboole_1])).
% 59.04/59.25  thf('32', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 59.04/59.25          | ~ (r1_tarski @ sk_B @ X0))),
% 59.04/59.25      inference('sup-', [status(thm)], ['30', '31'])).
% 59.04/59.25  thf('33', plain,
% 59.04/59.25      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))),
% 59.04/59.25      inference('sup-', [status(thm)], ['29', '32'])).
% 59.04/59.25  thf(t45_xboole_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( r1_tarski @ A @ B ) =>
% 59.04/59.25       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 59.04/59.25  thf('34', plain,
% 59.04/59.25      (![X11 : $i, X12 : $i]:
% 59.04/59.25         (((X12) = (k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))
% 59.04/59.25          | ~ (r1_tarski @ X11 @ X12))),
% 59.04/59.25      inference('cnf', [status(esa)], [t45_xboole_1])).
% 59.04/59.25  thf('35', plain,
% 59.04/59.25      (((k2_pre_topc @ sk_A @ sk_B)
% 59.04/59.25         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25            (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25             (k1_tops_1 @ sk_A @ sk_B))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['33', '34'])).
% 59.04/59.25  thf('36', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(dt_k2_pre_topc, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( ( l1_pre_topc @ A ) & 
% 59.04/59.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 59.04/59.25       ( m1_subset_1 @
% 59.04/59.25         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 59.04/59.25  thf('37', plain,
% 59.04/59.25      (![X34 : $i, X35 : $i]:
% 59.04/59.25         (~ (l1_pre_topc @ X34)
% 59.04/59.25          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 59.04/59.25          | (m1_subset_1 @ (k2_pre_topc @ X34 @ X35) @ 
% 59.04/59.25             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 59.04/59.25      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 59.04/59.25  thf('38', plain,
% 59.04/59.25      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.04/59.25        | ~ (l1_pre_topc @ sk_A))),
% 59.04/59.25      inference('sup-', [status(thm)], ['36', '37'])).
% 59.04/59.25  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('40', plain,
% 59.04/59.25      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['38', '39'])).
% 59.04/59.25  thf('41', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(dt_k1_tops_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( ( l1_pre_topc @ A ) & 
% 59.04/59.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 59.04/59.25       ( m1_subset_1 @
% 59.04/59.25         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 59.04/59.25  thf('42', plain,
% 59.04/59.25      (![X42 : $i, X43 : $i]:
% 59.04/59.25         (~ (l1_pre_topc @ X42)
% 59.04/59.25          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 59.04/59.25          | (m1_subset_1 @ (k1_tops_1 @ X42 @ X43) @ 
% 59.04/59.25             (k1_zfmisc_1 @ (u1_struct_0 @ X42))))),
% 59.04/59.25      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 59.04/59.25  thf('43', plain,
% 59.04/59.25      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.04/59.25        | ~ (l1_pre_topc @ sk_A))),
% 59.04/59.25      inference('sup-', [status(thm)], ['41', '42'])).
% 59.04/59.25  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('45', plain,
% 59.04/59.25      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['43', '44'])).
% 59.04/59.25  thf(t32_subset_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 59.04/59.25       ( ![C:$i]:
% 59.04/59.25         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 59.04/59.25           ( ( k7_subset_1 @ A @ B @ C ) =
% 59.04/59.25             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 59.04/59.25  thf('46', plain,
% 59.04/59.25      (![X31 : $i, X32 : $i, X33 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 59.04/59.25          | ((k7_subset_1 @ X32 @ X33 @ X31)
% 59.04/59.25              = (k9_subset_1 @ X32 @ X33 @ (k3_subset_1 @ X32 @ X31)))
% 59.04/59.25          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 59.04/59.25      inference('cnf', [status(esa)], [t32_subset_1])).
% 59.04/59.25  thf('47', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.04/59.25          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 59.04/59.25              (k1_tops_1 @ sk_A @ sk_B))
% 59.04/59.25              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 59.04/59.25                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.04/59.25                  (k1_tops_1 @ sk_A @ sk_B)))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['45', '46'])).
% 59.04/59.25  thf('48', plain,
% 59.04/59.25      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25         (k1_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['40', '47'])).
% 59.04/59.25  thf('49', plain,
% 59.04/59.25      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['38', '39'])).
% 59.04/59.25  thf('50', plain,
% 59.04/59.25      (![X28 : $i, X29 : $i, X30 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 59.04/59.25          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 59.04/59.25      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 59.04/59.25  thf('51', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 59.04/59.25      inference('sup-', [status(thm)], ['49', '50'])).
% 59.04/59.25  thf('52', plain,
% 59.04/59.25      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 59.04/59.25      inference('demod', [status(thm)], ['48', '51'])).
% 59.04/59.25  thf('53', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(d2_tops_1, axiom,
% 59.04/59.25    (![A:$i]:
% 59.04/59.25     ( ( l1_pre_topc @ A ) =>
% 59.04/59.25       ( ![B:$i]:
% 59.04/59.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.04/59.25           ( ( k2_tops_1 @ A @ B ) =
% 59.04/59.25             ( k9_subset_1 @
% 59.04/59.25               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 59.04/59.25               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 59.04/59.25  thf('54', plain,
% 59.04/59.25      (![X40 : $i, X41 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 59.04/59.25          | ((k2_tops_1 @ X41 @ X40)
% 59.04/59.25              = (k9_subset_1 @ (u1_struct_0 @ X41) @ 
% 59.04/59.25                 (k2_pre_topc @ X41 @ X40) @ 
% 59.04/59.25                 (k2_pre_topc @ X41 @ (k3_subset_1 @ (u1_struct_0 @ X41) @ X40))))
% 59.04/59.25          | ~ (l1_pre_topc @ X41))),
% 59.04/59.25      inference('cnf', [status(esa)], [d2_tops_1])).
% 59.04/59.25  thf('55', plain,
% 59.04/59.25      ((~ (l1_pre_topc @ sk_A)
% 59.04/59.25        | ((k2_tops_1 @ sk_A @ sk_B)
% 59.04/59.25            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.04/59.25               (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25               (k2_pre_topc @ sk_A @ 
% 59.04/59.25                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['53', '54'])).
% 59.04/59.25  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('57', plain,
% 59.04/59.25      (((k2_tops_1 @ sk_A @ sk_B)
% 59.04/59.25         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 59.04/59.25      inference('demod', [status(thm)], ['55', '56'])).
% 59.04/59.25  thf('58', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(dt_k3_subset_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 59.04/59.25       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 59.04/59.25  thf('59', plain,
% 59.04/59.25      (![X21 : $i, X22 : $i]:
% 59.04/59.25         ((m1_subset_1 @ (k3_subset_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 59.04/59.25          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 59.04/59.25      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 59.04/59.25  thf('60', plain,
% 59.04/59.25      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['58', '59'])).
% 59.04/59.25  thf('61', plain,
% 59.04/59.25      (![X34 : $i, X35 : $i]:
% 59.04/59.25         (~ (l1_pre_topc @ X34)
% 59.04/59.25          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 59.04/59.25          | (m1_subset_1 @ (k2_pre_topc @ X34 @ X35) @ 
% 59.04/59.25             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 59.04/59.25      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 59.04/59.25  thf('62', plain,
% 59.04/59.25      (((m1_subset_1 @ 
% 59.04/59.25         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 59.04/59.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.04/59.25        | ~ (l1_pre_topc @ sk_A))),
% 59.04/59.25      inference('sup-', [status(thm)], ['60', '61'])).
% 59.04/59.25  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('64', plain,
% 59.04/59.25      ((m1_subset_1 @ 
% 59.04/59.25        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['62', '63'])).
% 59.04/59.25  thf(involutiveness_k3_subset_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 59.04/59.25       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 59.04/59.25  thf('65', plain,
% 59.04/59.25      (![X23 : $i, X24 : $i]:
% 59.04/59.25         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 59.04/59.25          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 59.04/59.25      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 59.04/59.25  thf('66', plain,
% 59.04/59.25      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.04/59.25         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.04/59.25          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 59.04/59.25         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['64', '65'])).
% 59.04/59.25  thf('67', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(d1_tops_1, axiom,
% 59.04/59.25    (![A:$i]:
% 59.04/59.25     ( ( l1_pre_topc @ A ) =>
% 59.04/59.25       ( ![B:$i]:
% 59.04/59.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.04/59.25           ( ( k1_tops_1 @ A @ B ) =
% 59.04/59.25             ( k3_subset_1 @
% 59.04/59.25               ( u1_struct_0 @ A ) @ 
% 59.04/59.25               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 59.04/59.25  thf('68', plain,
% 59.04/59.25      (![X38 : $i, X39 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 59.04/59.25          | ((k1_tops_1 @ X39 @ X38)
% 59.04/59.25              = (k3_subset_1 @ (u1_struct_0 @ X39) @ 
% 59.04/59.25                 (k2_pre_topc @ X39 @ (k3_subset_1 @ (u1_struct_0 @ X39) @ X38))))
% 59.04/59.25          | ~ (l1_pre_topc @ X39))),
% 59.04/59.25      inference('cnf', [status(esa)], [d1_tops_1])).
% 59.04/59.25  thf('69', plain,
% 59.04/59.25      ((~ (l1_pre_topc @ sk_A)
% 59.04/59.25        | ((k1_tops_1 @ sk_A @ sk_B)
% 59.04/59.25            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.04/59.25               (k2_pre_topc @ sk_A @ 
% 59.04/59.25                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['67', '68'])).
% 59.04/59.25  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('71', plain,
% 59.04/59.25      (((k1_tops_1 @ sk_A @ sk_B)
% 59.04/59.25         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.04/59.25            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 59.04/59.25      inference('demod', [status(thm)], ['69', '70'])).
% 59.04/59.25  thf('72', plain,
% 59.04/59.25      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 59.04/59.25      inference('demod', [status(thm)], ['66', '71'])).
% 59.04/59.25  thf('73', plain,
% 59.04/59.25      (((k2_tops_1 @ sk_A @ sk_B)
% 59.04/59.25         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 59.04/59.25      inference('demod', [status(thm)], ['57', '72'])).
% 59.04/59.25  thf('74', plain,
% 59.04/59.25      (((k2_tops_1 @ sk_A @ sk_B)
% 59.04/59.25         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 59.04/59.25            (k1_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup+', [status(thm)], ['52', '73'])).
% 59.04/59.25  thf('75', plain,
% 59.04/59.25      (((k2_pre_topc @ sk_A @ sk_B)
% 59.04/59.25         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('demod', [status(thm)], ['35', '74'])).
% 59.04/59.25  thf('76', plain,
% 59.04/59.25      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['43', '44'])).
% 59.04/59.25  thf('77', plain,
% 59.04/59.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf(dt_k2_tops_1, axiom,
% 59.04/59.25    (![A:$i,B:$i]:
% 59.04/59.25     ( ( ( l1_pre_topc @ A ) & 
% 59.04/59.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 59.04/59.25       ( m1_subset_1 @
% 59.04/59.25         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 59.04/59.25  thf('78', plain,
% 59.04/59.25      (![X44 : $i, X45 : $i]:
% 59.04/59.25         (~ (l1_pre_topc @ X44)
% 59.04/59.25          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 59.04/59.25          | (m1_subset_1 @ (k2_tops_1 @ X44 @ X45) @ 
% 59.04/59.25             (k1_zfmisc_1 @ (u1_struct_0 @ X44))))),
% 59.04/59.25      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 59.04/59.25  thf('79', plain,
% 59.04/59.25      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.04/59.25        | ~ (l1_pre_topc @ sk_A))),
% 59.04/59.25      inference('sup-', [status(thm)], ['77', '78'])).
% 59.04/59.25  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 59.04/59.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.04/59.25  thf('81', plain,
% 59.04/59.25      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['79', '80'])).
% 59.04/59.25  thf(redefinition_k4_subset_1, axiom,
% 59.04/59.25    (![A:$i,B:$i,C:$i]:
% 59.04/59.25     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 59.04/59.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 59.04/59.25       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 59.04/59.25  thf('82', plain,
% 59.04/59.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 59.04/59.25          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 59.04/59.25          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 59.04/59.25      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 59.04/59.25  thf('83', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 59.04/59.25            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 59.04/59.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['81', '82'])).
% 59.04/59.25  thf('84', plain,
% 59.04/59.25      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25         (k1_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['76', '83'])).
% 59.04/59.25  thf('85', plain,
% 59.04/59.25      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['79', '80'])).
% 59.04/59.25  thf('86', plain,
% 59.04/59.25      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['43', '44'])).
% 59.04/59.25  thf('87', plain,
% 59.04/59.25      (![X25 : $i, X26 : $i, X27 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 59.04/59.25          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 59.04/59.25          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 59.04/59.25      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 59.04/59.25  thf('88', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 59.04/59.25            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 59.04/59.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['86', '87'])).
% 59.04/59.25  thf('89', plain,
% 59.04/59.25      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25         (k2_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['85', '88'])).
% 59.04/59.25  thf('90', plain,
% 59.04/59.25      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['79', '80'])).
% 59.04/59.25  thf('91', plain,
% 59.04/59.25      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.04/59.25      inference('demod', [status(thm)], ['43', '44'])).
% 59.04/59.25  thf(commutativity_k4_subset_1, axiom,
% 59.04/59.25    (![A:$i,B:$i,C:$i]:
% 59.04/59.25     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 59.04/59.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 59.04/59.25       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 59.04/59.25  thf('92', plain,
% 59.04/59.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 59.04/59.25         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 59.04/59.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 59.04/59.25          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k4_subset_1 @ X17 @ X18 @ X16)))),
% 59.04/59.25      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 59.04/59.25  thf('93', plain,
% 59.04/59.25      (![X0 : $i]:
% 59.04/59.25         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 59.04/59.25            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 59.04/59.25               (k1_tops_1 @ sk_A @ sk_B)))
% 59.04/59.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 59.04/59.25      inference('sup-', [status(thm)], ['91', '92'])).
% 59.04/59.25  thf('94', plain,
% 59.04/59.25      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25         (k2_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25            (k1_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup-', [status(thm)], ['90', '93'])).
% 59.04/59.25  thf('95', plain,
% 59.04/59.25      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 59.04/59.25            (k1_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup+', [status(thm)], ['89', '94'])).
% 59.04/59.25  thf('96', plain,
% 59.04/59.25      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 59.04/59.25         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup+', [status(thm)], ['84', '95'])).
% 59.04/59.25  thf('97', plain,
% 59.04/59.25      (((k2_pre_topc @ sk_A @ sk_B)
% 59.04/59.25         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 59.04/59.25      inference('sup+', [status(thm)], ['75', '96'])).
% 59.04/59.25  thf('98', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 59.04/59.25      inference('demod', [status(thm)], ['27', '28'])).
% 59.04/59.25  thf('99', plain,
% 59.04/59.25      (![X5 : $i, X7 : $i]:
% 59.04/59.25         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 59.04/59.25      inference('cnf', [status(esa)], [t37_xboole_1])).
% 59.04/59.25  thf('100', plain,
% 59.04/59.25      (((k4_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 59.04/59.25      inference('sup-', [status(thm)], ['98', '99'])).
% 59.04/59.25  thf('101', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 59.04/59.25      inference('demod', [status(thm)], ['24', '97', '100'])).
% 59.04/59.25  thf('102', plain, ($false), inference('simplify', [status(thm)], ['101'])).
% 59.04/59.25  
% 59.04/59.25  % SZS output end Refutation
% 59.04/59.25  
% 59.04/59.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
