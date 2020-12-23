%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VJm3GkLxlY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:41 EST 2020

% Result     : Theorem 11.29s
% Output     : Refutation 11.37s
% Verified   : 
% Statistics : Number of formulae       :  331 (2168 expanded)
%              Number of leaves         :   51 ( 748 expanded)
%              Depth                    :   24
%              Number of atoms          : 2720 (18142 expanded)
%              Number of equality atoms :  224 (1553 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ sk_B @ X0 ) ) )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ sk_B @ X0 ) )
      = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('22',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ sk_B @ X0 ) ) )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20','23'])).

thf('25',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('41',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('46',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k6_subset_1 @ X11 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','47'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('50',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('51',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k6_subset_1 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k5_xboole_0 @ X23 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('61',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','63'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('65',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('66',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('67',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k5_xboole_0 @ X23 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k6_subset_1 @ X11 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','77'])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('80',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['78','87'])).

thf('89',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['27','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('91',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X55 @ X56 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('92',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('96',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k2_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('97',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('98',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k3_tarski @ ( k2_tarski @ X38 @ X40 ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('103',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( ( k2_pre_topc @ X62 @ X61 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X62 ) @ X61 @ ( k2_tops_1 @ X62 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('110',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v4_pre_topc @ X53 @ X54 )
      | ( ( k2_pre_topc @ X54 @ X53 )
        = X53 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('111',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('119',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('120',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('121',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k6_subset_1 @ X43 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['107'])).

thf('124',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('126',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k6_subset_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('129',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k6_subset_1 @ X11 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('136',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('138',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('139',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('141',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('143',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('148',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k3_tarski @ ( k2_tarski @ X38 @ X40 ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['139','154'])).

thf('156',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['117','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('158',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X57 @ X58 ) @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('159',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['156','162'])).

thf('164',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['115'])).

thf('165',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['107'])).

thf('167',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['116','165','166'])).

thf('168',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['114','167'])).

thf('169',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','168'])).

thf('170',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['27','88'])).

thf('171',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['101','169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('173',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ ( k3_subset_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('178',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k6_subset_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('181',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['180','185'])).

thf('187',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('191',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k6_subset_1 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['189','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['188','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['176','179','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('200',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('203',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('204',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('208',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['206','211'])).

thf('213',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('214',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['212','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('220',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('222',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['212','217'])).

thf('226',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['201','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('231',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['229','232'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['198','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['197','234'])).

thf('236',plain,
    ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['171','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('238',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['236','237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('240',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('241',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k1_tops_1 @ X64 @ X63 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('242',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('245',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('247',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['245','250'])).

thf('252',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('253',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('254',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('256',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['251','256'])).

thf('258',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('260',plain,
    ( ( k6_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('262',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('264',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('265',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('267',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['257','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('270',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['238','239','268','269'])).

thf('271',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['115'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('273',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['116','165'])).

thf('275',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['273','274'])).

thf('276',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['265','266'])).

thf('277',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['270','277'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VJm3GkLxlY
% 0.14/0.37  % Computer   : n019.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 10:46:23 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 11.29/11.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.29/11.52  % Solved by: fo/fo7.sh
% 11.29/11.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.29/11.52  % done 19178 iterations in 11.024s
% 11.29/11.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.29/11.52  % SZS output start Refutation
% 11.29/11.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.29/11.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 11.29/11.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.29/11.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 11.29/11.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 11.29/11.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 11.29/11.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 11.29/11.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 11.29/11.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 11.29/11.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 11.29/11.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.29/11.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.29/11.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 11.29/11.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 11.29/11.52  thf(sk_A_type, type, sk_A: $i).
% 11.29/11.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 11.29/11.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.29/11.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.29/11.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 11.29/11.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.29/11.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 11.29/11.52  thf(sk_B_type, type, sk_B: $i).
% 11.29/11.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.29/11.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 11.29/11.52  thf(t3_boole, axiom,
% 11.29/11.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 11.29/11.52  thf('0', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 11.29/11.52      inference('cnf', [status(esa)], [t3_boole])).
% 11.29/11.52  thf(redefinition_k6_subset_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.29/11.52  thf('1', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('2', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 11.29/11.52      inference('demod', [status(thm)], ['0', '1'])).
% 11.29/11.52  thf(t77_tops_1, conjecture,
% 11.29/11.52    (![A:$i]:
% 11.29/11.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.29/11.52       ( ![B:$i]:
% 11.29/11.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.52           ( ( v4_pre_topc @ B @ A ) <=>
% 11.29/11.52             ( ( k2_tops_1 @ A @ B ) =
% 11.29/11.52               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 11.29/11.52  thf(zf_stmt_0, negated_conjecture,
% 11.29/11.52    (~( ![A:$i]:
% 11.29/11.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.29/11.52          ( ![B:$i]:
% 11.29/11.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.52              ( ( v4_pre_topc @ B @ A ) <=>
% 11.29/11.52                ( ( k2_tops_1 @ A @ B ) =
% 11.29/11.52                  ( k7_subset_1 @
% 11.29/11.52                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 11.29/11.52    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 11.29/11.52  thf('3', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf(t3_subset, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.29/11.52  thf('4', plain,
% 11.29/11.52      (![X50 : $i, X51 : $i]:
% 11.29/11.52         ((r1_tarski @ X50 @ X51) | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51)))),
% 11.29/11.52      inference('cnf', [status(esa)], [t3_subset])).
% 11.29/11.52  thf('5', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['3', '4'])).
% 11.29/11.52  thf(t36_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 11.29/11.52  thf('6', plain,
% 11.29/11.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 11.29/11.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.29/11.52  thf('7', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('8', plain,
% 11.29/11.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 11.29/11.52      inference('demod', [status(thm)], ['6', '7'])).
% 11.29/11.52  thf(t1_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i,C:$i]:
% 11.29/11.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 11.29/11.52       ( r1_tarski @ A @ C ) ))).
% 11.29/11.52  thf('9', plain,
% 11.29/11.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 11.29/11.52         (~ (r1_tarski @ X3 @ X4)
% 11.29/11.52          | ~ (r1_tarski @ X4 @ X5)
% 11.29/11.52          | (r1_tarski @ X3 @ X5))),
% 11.29/11.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 11.29/11.52  thf('10', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 11.29/11.52      inference('sup-', [status(thm)], ['8', '9'])).
% 11.29/11.52  thf('11', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['5', '10'])).
% 11.29/11.52  thf('12', plain,
% 11.29/11.52      (![X50 : $i, X52 : $i]:
% 11.29/11.52         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 11.29/11.52      inference('cnf', [status(esa)], [t3_subset])).
% 11.29/11.52  thf('13', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k6_subset_1 @ sk_B @ X0) @ 
% 11.29/11.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['11', '12'])).
% 11.29/11.52  thf(involutiveness_k3_subset_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.29/11.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 11.29/11.52  thf('14', plain,
% 11.29/11.52      (![X36 : $i, X37 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 11.29/11.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 11.29/11.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 11.29/11.52  thf('15', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k6_subset_1 @ sk_B @ X0)))
% 11.29/11.52           = (k6_subset_1 @ sk_B @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['13', '14'])).
% 11.29/11.52  thf('16', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k6_subset_1 @ sk_B @ X0) @ 
% 11.29/11.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['11', '12'])).
% 11.29/11.52  thf(d5_subset_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.29/11.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 11.29/11.52  thf('17', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.29/11.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 11.29/11.52  thf('18', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('19', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.29/11.52      inference('demod', [status(thm)], ['17', '18'])).
% 11.29/11.52  thf('20', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k6_subset_1 @ sk_B @ X0))
% 11.29/11.52           = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k6_subset_1 @ sk_B @ X0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['16', '19'])).
% 11.29/11.52  thf(dt_k6_subset_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 11.29/11.52  thf('21', plain,
% 11.29/11.52      (![X34 : $i, X35 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 11.29/11.52      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 11.29/11.52  thf('22', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.29/11.52      inference('demod', [status(thm)], ['17', '18'])).
% 11.29/11.52  thf('23', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 11.29/11.52           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['21', '22'])).
% 11.29/11.52  thf('24', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k6_subset_1 @ sk_B @ X0)))
% 11.29/11.52           = (k6_subset_1 @ sk_B @ X0))),
% 11.29/11.52      inference('demod', [status(thm)], ['15', '20', '23'])).
% 11.29/11.52  thf('25', plain,
% 11.29/11.52      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 11.29/11.52         = (k6_subset_1 @ sk_B @ k1_xboole_0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['2', '24'])).
% 11.29/11.52  thf('26', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 11.29/11.52      inference('demod', [status(thm)], ['0', '1'])).
% 11.29/11.52  thf('27', plain,
% 11.29/11.52      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 11.29/11.52      inference('demod', [status(thm)], ['25', '26'])).
% 11.29/11.52  thf(commutativity_k2_tarski, axiom,
% 11.29/11.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 11.29/11.52  thf('28', plain,
% 11.29/11.52      (![X25 : $i, X26 : $i]:
% 11.29/11.52         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 11.29/11.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 11.29/11.52  thf('29', plain,
% 11.29/11.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 11.29/11.52      inference('demod', [status(thm)], ['6', '7'])).
% 11.29/11.52  thf(t44_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i,C:$i]:
% 11.29/11.52     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 11.29/11.52       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 11.29/11.52  thf('30', plain,
% 11.29/11.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 11.29/11.52         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 11.29/11.52          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 11.29/11.52      inference('cnf', [status(esa)], [t44_xboole_1])).
% 11.29/11.52  thf(l51_zfmisc_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 11.29/11.52  thf('31', plain,
% 11.29/11.52      (![X27 : $i, X28 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 11.29/11.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 11.29/11.52  thf('32', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('33', plain,
% 11.29/11.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 11.29/11.52         ((r1_tarski @ X16 @ (k3_tarski @ (k2_tarski @ X17 @ X18)))
% 11.29/11.52          | ~ (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 11.29/11.52      inference('demod', [status(thm)], ['30', '31', '32'])).
% 11.29/11.52  thf('34', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['29', '33'])).
% 11.29/11.52  thf('35', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['3', '4'])).
% 11.29/11.52  thf('36', plain,
% 11.29/11.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 11.29/11.52         (~ (r1_tarski @ X3 @ X4)
% 11.29/11.52          | ~ (r1_tarski @ X4 @ X5)
% 11.29/11.52          | (r1_tarski @ X3 @ X5))),
% 11.29/11.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 11.29/11.52  thf('37', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['35', '36'])).
% 11.29/11.52  thf('38', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (r1_tarski @ sk_B @ 
% 11.29/11.52          (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['34', '37'])).
% 11.29/11.52  thf('39', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (r1_tarski @ sk_B @ 
% 11.29/11.52          (k3_tarski @ (k2_tarski @ (u1_struct_0 @ sk_A) @ X0)))),
% 11.29/11.52      inference('sup+', [status(thm)], ['28', '38'])).
% 11.29/11.52  thf(t43_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i,C:$i]:
% 11.29/11.52     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 11.29/11.52       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 11.29/11.52  thf('40', plain,
% 11.29/11.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.29/11.52         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 11.29/11.52          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 11.29/11.52      inference('cnf', [status(esa)], [t43_xboole_1])).
% 11.29/11.52  thf('41', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('42', plain,
% 11.29/11.52      (![X27 : $i, X28 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 11.29/11.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 11.29/11.52  thf('43', plain,
% 11.29/11.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.29/11.52         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 11.29/11.52          | ~ (r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X14 @ X15))))),
% 11.29/11.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 11.29/11.52  thf('44', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 11.29/11.52      inference('sup-', [status(thm)], ['39', '43'])).
% 11.29/11.52  thf(t38_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 11.29/11.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 11.29/11.52  thf('45', plain,
% 11.29/11.52      (![X10 : $i, X11 : $i]:
% 11.29/11.52         (((X10) = (k1_xboole_0))
% 11.29/11.52          | ~ (r1_tarski @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 11.29/11.52      inference('cnf', [status(esa)], [t38_xboole_1])).
% 11.29/11.52  thf('46', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('47', plain,
% 11.29/11.52      (![X10 : $i, X11 : $i]:
% 11.29/11.52         (((X10) = (k1_xboole_0))
% 11.29/11.52          | ~ (r1_tarski @ X10 @ (k6_subset_1 @ X11 @ X10)))),
% 11.29/11.52      inference('demod', [status(thm)], ['45', '46'])).
% 11.29/11.52  thf('48', plain,
% 11.29/11.52      (((k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['44', '47'])).
% 11.29/11.52  thf(t47_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.29/11.52  thf('49', plain,
% 11.29/11.52      (![X19 : $i, X20 : $i]:
% 11.29/11.52         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 11.29/11.52           = (k4_xboole_0 @ X19 @ X20))),
% 11.29/11.52      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.29/11.52  thf('50', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('51', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('52', plain,
% 11.29/11.52      (![X19 : $i, X20 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 11.29/11.52           = (k6_subset_1 @ X19 @ X20))),
% 11.29/11.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 11.29/11.52  thf(t98_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 11.29/11.52  thf('53', plain,
% 11.29/11.52      (![X23 : $i, X24 : $i]:
% 11.29/11.52         ((k2_xboole_0 @ X23 @ X24)
% 11.29/11.52           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 11.29/11.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 11.29/11.52  thf('54', plain,
% 11.29/11.52      (![X27 : $i, X28 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 11.29/11.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 11.29/11.52  thf('55', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('56', plain,
% 11.29/11.52      (![X23 : $i, X24 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X23 @ X24))
% 11.29/11.52           = (k5_xboole_0 @ X23 @ (k6_subset_1 @ X24 @ X23)))),
% 11.29/11.52      inference('demod', [status(thm)], ['53', '54', '55'])).
% 11.29/11.52  thf('57', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 11.29/11.52           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 11.29/11.52      inference('sup+', [status(thm)], ['52', '56'])).
% 11.29/11.52  thf('58', plain,
% 11.29/11.52      (![X25 : $i, X26 : $i]:
% 11.29/11.52         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 11.29/11.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 11.29/11.52  thf('59', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 11.29/11.52           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 11.29/11.52      inference('demod', [status(thm)], ['57', '58'])).
% 11.29/11.52  thf(t22_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 11.29/11.52  thf('60', plain,
% 11.29/11.52      (![X6 : $i, X7 : $i]:
% 11.29/11.52         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 11.29/11.52      inference('cnf', [status(esa)], [t22_xboole_1])).
% 11.29/11.52  thf('61', plain,
% 11.29/11.52      (![X27 : $i, X28 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 11.29/11.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 11.29/11.52  thf('62', plain,
% 11.29/11.52      (![X6 : $i, X7 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 11.29/11.52      inference('demod', [status(thm)], ['60', '61'])).
% 11.29/11.52  thf('63', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((X1)
% 11.29/11.52           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 11.29/11.52      inference('demod', [status(thm)], ['59', '62'])).
% 11.29/11.52  thf('64', plain,
% 11.29/11.52      (((sk_B)
% 11.29/11.52         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.29/11.52            k1_xboole_0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['48', '63'])).
% 11.29/11.52  thf(t1_boole, axiom,
% 11.29/11.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 11.29/11.52  thf('65', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 11.29/11.52      inference('cnf', [status(esa)], [t1_boole])).
% 11.29/11.52  thf('66', plain,
% 11.29/11.52      (![X27 : $i, X28 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 11.29/11.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 11.29/11.52  thf('67', plain,
% 11.29/11.52      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 11.29/11.52      inference('demod', [status(thm)], ['65', '66'])).
% 11.29/11.52  thf('68', plain,
% 11.29/11.52      (![X23 : $i, X24 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X23 @ X24))
% 11.29/11.52           = (k5_xboole_0 @ X23 @ (k6_subset_1 @ X24 @ X23)))),
% 11.29/11.52      inference('demod', [status(thm)], ['53', '54', '55'])).
% 11.29/11.52  thf('69', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((X0) = (k5_xboole_0 @ X0 @ (k6_subset_1 @ k1_xboole_0 @ X0)))),
% 11.29/11.52      inference('sup+', [status(thm)], ['67', '68'])).
% 11.29/11.52  thf('70', plain,
% 11.29/11.52      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 11.29/11.52      inference('demod', [status(thm)], ['65', '66'])).
% 11.29/11.52  thf('71', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['29', '33'])).
% 11.29/11.52  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.29/11.52      inference('sup+', [status(thm)], ['70', '71'])).
% 11.29/11.52  thf('73', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 11.29/11.52      inference('sup-', [status(thm)], ['8', '9'])).
% 11.29/11.52  thf('74', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ k1_xboole_0 @ X1) @ X0)),
% 11.29/11.52      inference('sup-', [status(thm)], ['72', '73'])).
% 11.29/11.52  thf('75', plain,
% 11.29/11.52      (![X10 : $i, X11 : $i]:
% 11.29/11.52         (((X10) = (k1_xboole_0))
% 11.29/11.52          | ~ (r1_tarski @ X10 @ (k6_subset_1 @ X11 @ X10)))),
% 11.29/11.52      inference('demod', [status(thm)], ['45', '46'])).
% 11.29/11.52  thf('76', plain,
% 11.29/11.52      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['74', '75'])).
% 11.29/11.52  thf('77', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 11.29/11.52      inference('demod', [status(thm)], ['69', '76'])).
% 11.29/11.52  thf('78', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('demod', [status(thm)], ['64', '77'])).
% 11.29/11.52  thf('79', plain,
% 11.29/11.52      (![X25 : $i, X26 : $i]:
% 11.29/11.52         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 11.29/11.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 11.29/11.52  thf(t12_setfam_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.29/11.52  thf('80', plain,
% 11.29/11.52      (![X48 : $i, X49 : $i]:
% 11.29/11.52         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 11.29/11.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.29/11.52  thf('81', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['79', '80'])).
% 11.29/11.52  thf('82', plain,
% 11.29/11.52      (![X48 : $i, X49 : $i]:
% 11.29/11.52         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 11.29/11.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 11.29/11.52  thf('83', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['81', '82'])).
% 11.29/11.52  thf(t100_xboole_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 11.29/11.52  thf('84', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k4_xboole_0 @ X0 @ X1)
% 11.29/11.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.29/11.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 11.29/11.52  thf('85', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('86', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X0 @ X1)
% 11.29/11.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.29/11.52      inference('demod', [status(thm)], ['84', '85'])).
% 11.29/11.52  thf('87', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X0 @ X1)
% 11.29/11.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 11.29/11.52      inference('sup+', [status(thm)], ['83', '86'])).
% 11.29/11.52  thf('88', plain,
% 11.29/11.52      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 11.29/11.52         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 11.29/11.52      inference('sup+', [status(thm)], ['78', '87'])).
% 11.29/11.52  thf('89', plain,
% 11.29/11.52      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 11.29/11.52      inference('demod', [status(thm)], ['27', '88'])).
% 11.29/11.52  thf('90', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf(dt_k2_tops_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( ( l1_pre_topc @ A ) & 
% 11.29/11.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.29/11.52       ( m1_subset_1 @
% 11.29/11.52         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 11.29/11.52  thf('91', plain,
% 11.29/11.52      (![X55 : $i, X56 : $i]:
% 11.29/11.52         (~ (l1_pre_topc @ X55)
% 11.29/11.52          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 11.29/11.52          | (m1_subset_1 @ (k2_tops_1 @ X55 @ X56) @ 
% 11.29/11.52             (k1_zfmisc_1 @ (u1_struct_0 @ X55))))),
% 11.29/11.52      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 11.29/11.52  thf('92', plain,
% 11.29/11.52      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 11.29/11.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.29/11.52        | ~ (l1_pre_topc @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['90', '91'])).
% 11.29/11.52  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('94', plain,
% 11.29/11.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 11.29/11.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('demod', [status(thm)], ['92', '93'])).
% 11.29/11.52  thf('95', plain,
% 11.29/11.52      (![X34 : $i, X35 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 11.29/11.52      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 11.29/11.52  thf(redefinition_k4_subset_1, axiom,
% 11.29/11.52    (![A:$i,B:$i,C:$i]:
% 11.29/11.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 11.29/11.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 11.29/11.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 11.29/11.52  thf('96', plain,
% 11.29/11.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 11.29/11.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 11.29/11.52          | ((k4_subset_1 @ X39 @ X38 @ X40) = (k2_xboole_0 @ X38 @ X40)))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 11.29/11.52  thf('97', plain,
% 11.29/11.52      (![X27 : $i, X28 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 11.29/11.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 11.29/11.52  thf('98', plain,
% 11.29/11.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 11.29/11.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 11.29/11.52          | ((k4_subset_1 @ X39 @ X38 @ X40)
% 11.29/11.52              = (k3_tarski @ (k2_tarski @ X38 @ X40))))),
% 11.29/11.52      inference('demod', [status(thm)], ['96', '97'])).
% 11.29/11.52  thf('99', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 11.29/11.52            = (k3_tarski @ (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ X2)))
% 11.29/11.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['95', '98'])).
% 11.29/11.52  thf('100', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.29/11.52           (k2_tops_1 @ sk_A @ sk_B))
% 11.29/11.52           = (k3_tarski @ 
% 11.29/11.52              (k2_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 11.29/11.52               (k2_tops_1 @ sk_A @ sk_B))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['94', '99'])).
% 11.29/11.52  thf('101', plain,
% 11.29/11.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 11.29/11.52         = (k3_tarski @ 
% 11.29/11.52            (k2_tarski @ 
% 11.29/11.52             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52              (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 11.29/11.52             (k2_tops_1 @ sk_A @ sk_B))))),
% 11.29/11.52      inference('sup+', [status(thm)], ['89', '100'])).
% 11.29/11.52  thf('102', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf(t65_tops_1, axiom,
% 11.29/11.52    (![A:$i]:
% 11.29/11.52     ( ( l1_pre_topc @ A ) =>
% 11.29/11.52       ( ![B:$i]:
% 11.29/11.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.52           ( ( k2_pre_topc @ A @ B ) =
% 11.29/11.52             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 11.29/11.52  thf('103', plain,
% 11.29/11.52      (![X61 : $i, X62 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 11.29/11.52          | ((k2_pre_topc @ X62 @ X61)
% 11.29/11.52              = (k4_subset_1 @ (u1_struct_0 @ X62) @ X61 @ 
% 11.29/11.52                 (k2_tops_1 @ X62 @ X61)))
% 11.29/11.52          | ~ (l1_pre_topc @ X62))),
% 11.29/11.52      inference('cnf', [status(esa)], [t65_tops_1])).
% 11.29/11.52  thf('104', plain,
% 11.29/11.52      ((~ (l1_pre_topc @ sk_A)
% 11.29/11.52        | ((k2_pre_topc @ sk_A @ sk_B)
% 11.29/11.52            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52               (k2_tops_1 @ sk_A @ sk_B))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['102', '103'])).
% 11.29/11.52  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('106', plain,
% 11.29/11.52      (((k2_pre_topc @ sk_A @ sk_B)
% 11.29/11.52         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52            (k2_tops_1 @ sk_A @ sk_B)))),
% 11.29/11.52      inference('demod', [status(thm)], ['104', '105'])).
% 11.29/11.52  thf('107', plain,
% 11.29/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52             (k1_tops_1 @ sk_A @ sk_B)))
% 11.29/11.52        | (v4_pre_topc @ sk_B @ sk_A))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('108', plain,
% 11.29/11.52      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 11.29/11.52      inference('split', [status(esa)], ['107'])).
% 11.29/11.52  thf('109', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf(t52_pre_topc, axiom,
% 11.29/11.52    (![A:$i]:
% 11.29/11.52     ( ( l1_pre_topc @ A ) =>
% 11.29/11.52       ( ![B:$i]:
% 11.29/11.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 11.29/11.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 11.29/11.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 11.29/11.52  thf('110', plain,
% 11.29/11.52      (![X53 : $i, X54 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 11.29/11.52          | ~ (v4_pre_topc @ X53 @ X54)
% 11.29/11.52          | ((k2_pre_topc @ X54 @ X53) = (X53))
% 11.29/11.52          | ~ (l1_pre_topc @ X54))),
% 11.29/11.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 11.29/11.52  thf('111', plain,
% 11.29/11.52      ((~ (l1_pre_topc @ sk_A)
% 11.29/11.52        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 11.29/11.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['109', '110'])).
% 11.29/11.52  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('113', plain,
% 11.29/11.52      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 11.29/11.52      inference('demod', [status(thm)], ['111', '112'])).
% 11.29/11.52  thf('114', plain,
% 11.29/11.52      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 11.29/11.52         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['108', '113'])).
% 11.29/11.52  thf('115', plain,
% 11.29/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52              (k1_tops_1 @ sk_A @ sk_B)))
% 11.29/11.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('116', plain,
% 11.29/11.52      (~
% 11.29/11.52       (((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 11.29/11.52       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 11.29/11.52      inference('split', [status(esa)], ['115'])).
% 11.29/11.52  thf('117', plain,
% 11.29/11.52      (((k2_pre_topc @ sk_A @ sk_B)
% 11.29/11.52         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52            (k2_tops_1 @ sk_A @ sk_B)))),
% 11.29/11.52      inference('demod', [status(thm)], ['104', '105'])).
% 11.29/11.52  thf('118', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf(redefinition_k7_subset_1, axiom,
% 11.29/11.52    (![A:$i,B:$i,C:$i]:
% 11.29/11.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.29/11.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 11.29/11.52  thf('119', plain,
% 11.29/11.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 11.29/11.52          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 11.29/11.52  thf('120', plain,
% 11.29/11.52      (![X41 : $i, X42 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 11.29/11.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 11.29/11.52  thf('121', plain,
% 11.29/11.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 11.29/11.52          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k6_subset_1 @ X43 @ X45)))),
% 11.29/11.52      inference('demod', [status(thm)], ['119', '120'])).
% 11.29/11.52  thf('122', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 11.29/11.52           = (k6_subset_1 @ sk_B @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['118', '121'])).
% 11.29/11.52  thf('123', plain,
% 11.29/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52             (k1_tops_1 @ sk_A @ sk_B))))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('split', [status(esa)], ['107'])).
% 11.29/11.52  thf('124', plain,
% 11.29/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('sup+', [status(thm)], ['122', '123'])).
% 11.29/11.52  thf('125', plain,
% 11.29/11.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 11.29/11.52      inference('demod', [status(thm)], ['6', '7'])).
% 11.29/11.52  thf('126', plain,
% 11.29/11.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.29/11.52         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 11.29/11.52          | ~ (r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X14 @ X15))))),
% 11.29/11.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 11.29/11.52  thf('127', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         (r1_tarski @ 
% 11.29/11.52          (k6_subset_1 @ 
% 11.29/11.52           (k6_subset_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2) @ X1) @ 
% 11.29/11.52          X0)),
% 11.29/11.52      inference('sup-', [status(thm)], ['125', '126'])).
% 11.29/11.52  thf('128', plain,
% 11.29/11.52      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['74', '75'])).
% 11.29/11.52  thf('129', plain,
% 11.29/11.52      (![X10 : $i, X11 : $i]:
% 11.29/11.52         (((X10) = (k1_xboole_0))
% 11.29/11.52          | ~ (r1_tarski @ X10 @ (k6_subset_1 @ X11 @ X10)))),
% 11.29/11.52      inference('demod', [status(thm)], ['45', '46'])).
% 11.29/11.52  thf('130', plain,
% 11.29/11.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['128', '129'])).
% 11.29/11.52  thf('131', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k6_subset_1 @ 
% 11.29/11.52           (k6_subset_1 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ X1) @ 
% 11.29/11.52           X0) = (k1_xboole_0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['127', '130'])).
% 11.29/11.52  thf('132', plain,
% 11.29/11.52      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 11.29/11.52      inference('demod', [status(thm)], ['65', '66'])).
% 11.29/11.52  thf('133', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 11.29/11.52      inference('demod', [status(thm)], ['131', '132'])).
% 11.29/11.52  thf('134', plain,
% 11.29/11.52      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('sup+', [status(thm)], ['124', '133'])).
% 11.29/11.52  thf('135', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((X1)
% 11.29/11.52           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 11.29/11.52      inference('demod', [status(thm)], ['59', '62'])).
% 11.29/11.52  thf('136', plain,
% 11.29/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k5_xboole_0 @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 11.29/11.52             k1_xboole_0)))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('sup+', [status(thm)], ['134', '135'])).
% 11.29/11.52  thf('137', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['81', '82'])).
% 11.29/11.52  thf('138', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 11.29/11.52      inference('demod', [status(thm)], ['69', '76'])).
% 11.29/11.52  thf('139', plain,
% 11.29/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('demod', [status(thm)], ['136', '137', '138'])).
% 11.29/11.52  thf('140', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['3', '4'])).
% 11.29/11.52  thf('141', plain,
% 11.29/11.52      (![X6 : $i, X7 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 11.29/11.52      inference('demod', [status(thm)], ['60', '61'])).
% 11.29/11.52  thf('142', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['29', '33'])).
% 11.29/11.52  thf('143', plain,
% 11.29/11.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 11.29/11.52         (~ (r1_tarski @ X3 @ X4)
% 11.29/11.52          | ~ (r1_tarski @ X4 @ X5)
% 11.29/11.52          | (r1_tarski @ X3 @ X5))),
% 11.29/11.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 11.29/11.52  thf('144', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         ((r1_tarski @ X0 @ X2)
% 11.29/11.52          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2))),
% 11.29/11.52      inference('sup-', [status(thm)], ['142', '143'])).
% 11.29/11.52  thf('145', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 11.29/11.52      inference('sup-', [status(thm)], ['141', '144'])).
% 11.29/11.52  thf('146', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['140', '145'])).
% 11.29/11.52  thf('147', plain,
% 11.29/11.52      (![X50 : $i, X52 : $i]:
% 11.29/11.52         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 11.29/11.52      inference('cnf', [status(esa)], [t3_subset])).
% 11.29/11.52  thf('148', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 11.29/11.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['146', '147'])).
% 11.29/11.52  thf('149', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('150', plain,
% 11.29/11.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 11.29/11.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 11.29/11.52          | ((k4_subset_1 @ X39 @ X38 @ X40)
% 11.29/11.52              = (k3_tarski @ (k2_tarski @ X38 @ X40))))),
% 11.29/11.52      inference('demod', [status(thm)], ['96', '97'])).
% 11.29/11.52  thf('151', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 11.29/11.52            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 11.29/11.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['149', '150'])).
% 11.29/11.52  thf('152', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52           (k3_xboole_0 @ sk_B @ X0))
% 11.29/11.52           = (k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ X0))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['148', '151'])).
% 11.29/11.52  thf('153', plain,
% 11.29/11.52      (![X6 : $i, X7 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 11.29/11.52      inference('demod', [status(thm)], ['60', '61'])).
% 11.29/11.52  thf('154', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52           (k3_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 11.29/11.52      inference('demod', [status(thm)], ['152', '153'])).
% 11.29/11.52  thf('155', plain,
% 11.29/11.52      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 11.29/11.52          = (sk_B)))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('sup+', [status(thm)], ['139', '154'])).
% 11.29/11.52  thf('156', plain,
% 11.29/11.52      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('sup+', [status(thm)], ['117', '155'])).
% 11.29/11.52  thf('157', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf(fc1_tops_1, axiom,
% 11.29/11.52    (![A:$i,B:$i]:
% 11.29/11.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 11.29/11.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.29/11.52       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 11.29/11.52  thf('158', plain,
% 11.29/11.52      (![X57 : $i, X58 : $i]:
% 11.29/11.52         (~ (l1_pre_topc @ X57)
% 11.29/11.52          | ~ (v2_pre_topc @ X57)
% 11.29/11.52          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 11.29/11.52          | (v4_pre_topc @ (k2_pre_topc @ X57 @ X58) @ X57))),
% 11.29/11.52      inference('cnf', [status(esa)], [fc1_tops_1])).
% 11.29/11.52  thf('159', plain,
% 11.29/11.52      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 11.29/11.52        | ~ (v2_pre_topc @ sk_A)
% 11.29/11.52        | ~ (l1_pre_topc @ sk_A))),
% 11.29/11.52      inference('sup-', [status(thm)], ['157', '158'])).
% 11.29/11.52  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('162', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 11.29/11.52      inference('demod', [status(thm)], ['159', '160', '161'])).
% 11.29/11.52  thf('163', plain,
% 11.29/11.52      (((v4_pre_topc @ sk_B @ sk_A))
% 11.29/11.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.29/11.52      inference('sup+', [status(thm)], ['156', '162'])).
% 11.29/11.52  thf('164', plain,
% 11.29/11.52      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 11.29/11.52      inference('split', [status(esa)], ['115'])).
% 11.29/11.52  thf('165', plain,
% 11.29/11.52      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 11.29/11.52       ~
% 11.29/11.52       (((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52             (k1_tops_1 @ sk_A @ sk_B))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['163', '164'])).
% 11.29/11.52  thf('166', plain,
% 11.29/11.52      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 11.29/11.52       (((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52             (k1_tops_1 @ sk_A @ sk_B))))),
% 11.29/11.52      inference('split', [status(esa)], ['107'])).
% 11.29/11.52  thf('167', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 11.29/11.52      inference('sat_resolution*', [status(thm)], ['116', '165', '166'])).
% 11.29/11.52  thf('168', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 11.29/11.52      inference('simpl_trail', [status(thm)], ['114', '167'])).
% 11.29/11.52  thf('169', plain,
% 11.29/11.52      (((sk_B)
% 11.29/11.52         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52            (k2_tops_1 @ sk_A @ sk_B)))),
% 11.29/11.52      inference('demod', [status(thm)], ['106', '168'])).
% 11.29/11.52  thf('170', plain,
% 11.29/11.52      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 11.29/11.52         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 11.29/11.52      inference('demod', [status(thm)], ['27', '88'])).
% 11.29/11.52  thf('171', plain,
% 11.29/11.52      (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 11.29/11.52      inference('demod', [status(thm)], ['101', '169', '170'])).
% 11.29/11.52  thf('172', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['29', '33'])).
% 11.29/11.52  thf('173', plain,
% 11.29/11.52      (![X50 : $i, X52 : $i]:
% 11.29/11.52         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 11.29/11.52      inference('cnf', [status(esa)], [t3_subset])).
% 11.29/11.52  thf('174', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (m1_subset_1 @ X0 @ 
% 11.29/11.52          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['172', '173'])).
% 11.29/11.52  thf('175', plain,
% 11.29/11.52      (![X36 : $i, X37 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 11.29/11.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 11.29/11.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 11.29/11.52  thf('176', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ 
% 11.29/11.52           (k3_subset_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X0)) = (
% 11.29/11.52           X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['174', '175'])).
% 11.29/11.52  thf('177', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (m1_subset_1 @ X0 @ 
% 11.29/11.52          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['172', '173'])).
% 11.29/11.52  thf('178', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.29/11.52      inference('demod', [status(thm)], ['17', '18'])).
% 11.29/11.52  thf('179', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X0)
% 11.29/11.52           = (k6_subset_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['177', '178'])).
% 11.29/11.52  thf('180', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['81', '82'])).
% 11.29/11.52  thf('181', plain,
% 11.29/11.52      (![X6 : $i, X7 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 11.29/11.52      inference('demod', [status(thm)], ['60', '61'])).
% 11.29/11.52  thf('182', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['29', '33'])).
% 11.29/11.52  thf('183', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 11.29/11.52      inference('sup+', [status(thm)], ['181', '182'])).
% 11.29/11.52  thf('184', plain,
% 11.29/11.52      (![X50 : $i, X52 : $i]:
% 11.29/11.52         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 11.29/11.52      inference('cnf', [status(esa)], [t3_subset])).
% 11.29/11.52  thf('185', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['183', '184'])).
% 11.29/11.52  thf('186', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['180', '185'])).
% 11.29/11.52  thf('187', plain,
% 11.29/11.52      (![X36 : $i, X37 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 11.29/11.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 11.29/11.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 11.29/11.52  thf('188', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 11.29/11.52           = (k3_xboole_0 @ X1 @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['186', '187'])).
% 11.29/11.52  thf('189', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['81', '82'])).
% 11.29/11.52  thf('190', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['183', '184'])).
% 11.29/11.52  thf('191', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.29/11.52      inference('demod', [status(thm)], ['17', '18'])).
% 11.29/11.52  thf('192', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 11.29/11.52           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['190', '191'])).
% 11.29/11.52  thf('193', plain,
% 11.29/11.52      (![X19 : $i, X20 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 11.29/11.52           = (k6_subset_1 @ X19 @ X20))),
% 11.29/11.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 11.29/11.52  thf('194', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 11.29/11.52           = (k6_subset_1 @ X0 @ X1))),
% 11.29/11.52      inference('demod', [status(thm)], ['192', '193'])).
% 11.29/11.52  thf('195', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.29/11.52           = (k6_subset_1 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['189', '194'])).
% 11.29/11.52  thf('196', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 11.29/11.52           = (k3_xboole_0 @ X1 @ X0))),
% 11.29/11.52      inference('demod', [status(thm)], ['188', '195'])).
% 11.29/11.52  thf('197', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_xboole_0 @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0))) = (X0))),
% 11.29/11.52      inference('demod', [status(thm)], ['176', '179', '196'])).
% 11.29/11.52  thf('198', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['81', '82'])).
% 11.29/11.52  thf('199', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 11.29/11.52      inference('sup+', [status(thm)], ['181', '182'])).
% 11.29/11.52  thf('200', plain,
% 11.29/11.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 11.29/11.52         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 11.29/11.52          | ~ (r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X14 @ X15))))),
% 11.29/11.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 11.29/11.52  thf('201', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         (r1_tarski @ 
% 11.29/11.52          (k6_subset_1 @ 
% 11.29/11.52           (k3_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2) @ X1) @ 
% 11.29/11.52          X0)),
% 11.29/11.52      inference('sup-', [status(thm)], ['199', '200'])).
% 11.29/11.52  thf('202', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 11.29/11.52      inference('sup+', [status(thm)], ['70', '71'])).
% 11.29/11.52  thf('203', plain,
% 11.29/11.52      (![X50 : $i, X52 : $i]:
% 11.29/11.52         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 11.29/11.52      inference('cnf', [status(esa)], [t3_subset])).
% 11.29/11.52  thf('204', plain,
% 11.29/11.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['202', '203'])).
% 11.29/11.52  thf('205', plain,
% 11.29/11.52      (![X36 : $i, X37 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 11.29/11.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 11.29/11.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 11.29/11.52  thf('206', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['204', '205'])).
% 11.29/11.52  thf('207', plain,
% 11.29/11.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['202', '203'])).
% 11.29/11.52  thf('208', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.29/11.52      inference('demod', [status(thm)], ['17', '18'])).
% 11.29/11.52  thf('209', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['207', '208'])).
% 11.29/11.52  thf('210', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 11.29/11.52      inference('demod', [status(thm)], ['0', '1'])).
% 11.29/11.52  thf('211', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 11.29/11.52      inference('demod', [status(thm)], ['209', '210'])).
% 11.29/11.52  thf('212', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 11.29/11.52      inference('demod', [status(thm)], ['206', '211'])).
% 11.29/11.52  thf('213', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 11.29/11.52      inference('demod', [status(thm)], ['0', '1'])).
% 11.29/11.52  thf('214', plain,
% 11.29/11.52      (![X34 : $i, X35 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 11.29/11.52      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 11.29/11.52  thf('215', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['213', '214'])).
% 11.29/11.52  thf('216', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.29/11.52      inference('demod', [status(thm)], ['17', '18'])).
% 11.29/11.52  thf('217', plain,
% 11.29/11.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k6_subset_1 @ X0 @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['215', '216'])).
% 11.29/11.52  thf('218', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['212', '217'])).
% 11.29/11.52  thf('219', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((X1)
% 11.29/11.52           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 11.29/11.52      inference('demod', [status(thm)], ['59', '62'])).
% 11.29/11.52  thf('220', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((X0) = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['218', '219'])).
% 11.29/11.52  thf('221', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 11.29/11.52      inference('demod', [status(thm)], ['69', '76'])).
% 11.29/11.52  thf('222', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 11.29/11.52      inference('demod', [status(thm)], ['220', '221'])).
% 11.29/11.52  thf('223', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X0 @ X1)
% 11.29/11.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.29/11.52      inference('demod', [status(thm)], ['84', '85'])).
% 11.29/11.52  thf('224', plain,
% 11.29/11.52      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['222', '223'])).
% 11.29/11.52  thf('225', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['212', '217'])).
% 11.29/11.52  thf('226', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['224', '225'])).
% 11.29/11.52  thf('227', plain,
% 11.29/11.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['128', '129'])).
% 11.29/11.52  thf('228', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 11.29/11.52      inference('sup-', [status(thm)], ['226', '227'])).
% 11.29/11.52  thf('229', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.29/11.52         ((k6_subset_1 @ 
% 11.29/11.52           (k3_xboole_0 @ 
% 11.29/11.52            (k3_tarski @ (k2_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0))) @ X2) @ 
% 11.29/11.52           X1) = (k1_xboole_0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['201', '228'])).
% 11.29/11.52  thf('230', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['224', '225'])).
% 11.29/11.52  thf('231', plain,
% 11.29/11.52      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 11.29/11.52      inference('demod', [status(thm)], ['65', '66'])).
% 11.29/11.52  thf('232', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_tarski @ (k2_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0))) = (X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['230', '231'])).
% 11.29/11.52  thf('233', plain,
% 11.29/11.52      (![X1 : $i, X2 : $i]:
% 11.29/11.52         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 11.29/11.52      inference('demod', [status(thm)], ['229', '232'])).
% 11.29/11.52  thf('234', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['198', '233'])).
% 11.29/11.52  thf('235', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k6_subset_1 @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 11.29/11.52           = (k1_xboole_0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['197', '234'])).
% 11.29/11.52  thf('236', plain,
% 11.29/11.52      (((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['171', '235'])).
% 11.29/11.52  thf('237', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((X1)
% 11.29/11.52           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 11.29/11.52      inference('demod', [status(thm)], ['59', '62'])).
% 11.29/11.52  thf('238', plain,
% 11.29/11.52      (((k2_tops_1 @ sk_A @ sk_B)
% 11.29/11.52         = (k5_xboole_0 @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 11.29/11.52            k1_xboole_0))),
% 11.29/11.52      inference('sup+', [status(thm)], ['236', '237'])).
% 11.29/11.52  thf('239', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup+', [status(thm)], ['81', '82'])).
% 11.29/11.52  thf('240', plain,
% 11.29/11.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf(t74_tops_1, axiom,
% 11.29/11.52    (![A:$i]:
% 11.29/11.52     ( ( l1_pre_topc @ A ) =>
% 11.29/11.52       ( ![B:$i]:
% 11.29/11.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.29/11.52           ( ( k1_tops_1 @ A @ B ) =
% 11.29/11.52             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 11.29/11.52  thf('241', plain,
% 11.29/11.52      (![X63 : $i, X64 : $i]:
% 11.29/11.52         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 11.29/11.52          | ((k1_tops_1 @ X64 @ X63)
% 11.29/11.52              = (k7_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 11.29/11.52                 (k2_tops_1 @ X64 @ X63)))
% 11.29/11.52          | ~ (l1_pre_topc @ X64))),
% 11.29/11.52      inference('cnf', [status(esa)], [t74_tops_1])).
% 11.29/11.52  thf('242', plain,
% 11.29/11.52      ((~ (l1_pre_topc @ sk_A)
% 11.29/11.52        | ((k1_tops_1 @ sk_A @ sk_B)
% 11.29/11.52            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.29/11.52               (k2_tops_1 @ sk_A @ sk_B))))),
% 11.29/11.52      inference('sup-', [status(thm)], ['240', '241'])).
% 11.29/11.52  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 11.29/11.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.29/11.52  thf('244', plain,
% 11.29/11.52      (![X0 : $i]:
% 11.29/11.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 11.29/11.52           = (k6_subset_1 @ sk_B @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['118', '121'])).
% 11.29/11.52  thf('245', plain,
% 11.29/11.52      (((k1_tops_1 @ sk_A @ sk_B)
% 11.29/11.52         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 11.29/11.52      inference('demod', [status(thm)], ['242', '243', '244'])).
% 11.29/11.52  thf('246', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 11.29/11.52      inference('sup-', [status(thm)], ['183', '184'])).
% 11.29/11.52  thf('247', plain,
% 11.29/11.52      (![X36 : $i, X37 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 11.29/11.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 11.29/11.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 11.29/11.52  thf('248', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 11.29/11.52           = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('sup-', [status(thm)], ['246', '247'])).
% 11.29/11.52  thf('249', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 11.29/11.52           = (k6_subset_1 @ X0 @ X1))),
% 11.29/11.52      inference('demod', [status(thm)], ['192', '193'])).
% 11.29/11.52  thf('250', plain,
% 11.29/11.52      (![X0 : $i, X1 : $i]:
% 11.29/11.52         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 11.29/11.52           = (k3_xboole_0 @ X0 @ X1))),
% 11.29/11.52      inference('demod', [status(thm)], ['248', '249'])).
% 11.29/11.52  thf('251', plain,
% 11.29/11.52      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.29/11.52         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 11.29/11.52      inference('sup+', [status(thm)], ['245', '250'])).
% 11.29/11.52  thf('252', plain,
% 11.29/11.52      (((k1_tops_1 @ sk_A @ sk_B)
% 11.29/11.52         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 11.29/11.52      inference('demod', [status(thm)], ['242', '243', '244'])).
% 11.29/11.52  thf('253', plain,
% 11.29/11.52      (![X34 : $i, X35 : $i]:
% 11.29/11.52         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 11.29/11.52      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 11.29/11.52  thf('254', plain,
% 11.29/11.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 11.29/11.52      inference('sup+', [status(thm)], ['252', '253'])).
% 11.29/11.52  thf('255', plain,
% 11.29/11.52      (![X30 : $i, X31 : $i]:
% 11.29/11.52         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 11.29/11.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 11.37/11.52      inference('demod', [status(thm)], ['17', '18'])).
% 11.37/11.52  thf('256', plain,
% 11.37/11.52      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.37/11.52         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('sup-', [status(thm)], ['254', '255'])).
% 11.37/11.52  thf('257', plain,
% 11.37/11.52      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.37/11.52         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('demod', [status(thm)], ['251', '256'])).
% 11.37/11.52  thf('258', plain,
% 11.37/11.52      (((k1_tops_1 @ sk_A @ sk_B)
% 11.37/11.52         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('demod', [status(thm)], ['242', '243', '244'])).
% 11.37/11.52  thf('259', plain,
% 11.37/11.52      (![X0 : $i, X1 : $i]:
% 11.37/11.52         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 11.37/11.52      inference('demod', [status(thm)], ['131', '132'])).
% 11.37/11.52  thf('260', plain,
% 11.37/11.52      (((k6_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 11.37/11.52      inference('sup+', [status(thm)], ['258', '259'])).
% 11.37/11.52  thf('261', plain,
% 11.37/11.52      (![X0 : $i, X1 : $i]:
% 11.37/11.52         ((X1)
% 11.37/11.52           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 11.37/11.52      inference('demod', [status(thm)], ['59', '62'])).
% 11.37/11.52  thf('262', plain,
% 11.37/11.52      (((k1_tops_1 @ sk_A @ sk_B)
% 11.37/11.52         = (k5_xboole_0 @ (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 11.37/11.52            k1_xboole_0))),
% 11.37/11.52      inference('sup+', [status(thm)], ['260', '261'])).
% 11.37/11.52  thf('263', plain,
% 11.37/11.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.37/11.52      inference('sup+', [status(thm)], ['81', '82'])).
% 11.37/11.52  thf('264', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 11.37/11.52      inference('demod', [status(thm)], ['69', '76'])).
% 11.37/11.52  thf('265', plain,
% 11.37/11.52      (((k1_tops_1 @ sk_A @ sk_B)
% 11.37/11.52         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('demod', [status(thm)], ['262', '263', '264'])).
% 11.37/11.52  thf('266', plain,
% 11.37/11.52      (![X0 : $i, X1 : $i]:
% 11.37/11.52         ((k6_subset_1 @ X0 @ X1)
% 11.37/11.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 11.37/11.52      inference('demod', [status(thm)], ['84', '85'])).
% 11.37/11.52  thf('267', plain,
% 11.37/11.52      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.37/11.52         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('sup+', [status(thm)], ['265', '266'])).
% 11.37/11.52  thf('268', plain,
% 11.37/11.52      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.37/11.52         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('demod', [status(thm)], ['257', '267'])).
% 11.37/11.52  thf('269', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 11.37/11.52      inference('demod', [status(thm)], ['69', '76'])).
% 11.37/11.52  thf('270', plain,
% 11.37/11.52      (((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('demod', [status(thm)], ['238', '239', '268', '269'])).
% 11.37/11.52  thf('271', plain,
% 11.37/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.37/11.52              (k1_tops_1 @ sk_A @ sk_B))))
% 11.37/11.52         <= (~
% 11.37/11.52             (((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.37/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.37/11.52      inference('split', [status(esa)], ['115'])).
% 11.37/11.52  thf('272', plain,
% 11.37/11.52      (![X0 : $i]:
% 11.37/11.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 11.37/11.52           = (k6_subset_1 @ sk_B @ X0))),
% 11.37/11.52      inference('sup-', [status(thm)], ['118', '121'])).
% 11.37/11.52  thf('273', plain,
% 11.37/11.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.37/11.52         <= (~
% 11.37/11.52             (((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.37/11.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 11.37/11.52      inference('demod', [status(thm)], ['271', '272'])).
% 11.37/11.52  thf('274', plain,
% 11.37/11.52      (~
% 11.37/11.52       (((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 11.37/11.52             (k1_tops_1 @ sk_A @ sk_B))))),
% 11.37/11.52      inference('sat_resolution*', [status(thm)], ['116', '165'])).
% 11.37/11.52  thf('275', plain,
% 11.37/11.52      (((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52         != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('simpl_trail', [status(thm)], ['273', '274'])).
% 11.37/11.52  thf('276', plain,
% 11.37/11.52      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.37/11.52         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('sup+', [status(thm)], ['265', '266'])).
% 11.37/11.52  thf('277', plain,
% 11.37/11.52      (((k2_tops_1 @ sk_A @ sk_B)
% 11.37/11.52         != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.37/11.52      inference('demod', [status(thm)], ['275', '276'])).
% 11.37/11.52  thf('278', plain, ($false),
% 11.37/11.52      inference('simplify_reflect-', [status(thm)], ['270', '277'])).
% 11.37/11.52  
% 11.37/11.52  % SZS output end Refutation
% 11.37/11.52  
% 11.37/11.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
