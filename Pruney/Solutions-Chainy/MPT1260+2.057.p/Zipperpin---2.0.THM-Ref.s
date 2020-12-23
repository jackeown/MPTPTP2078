%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9UjVz7QfSr

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:31 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 942 expanded)
%              Number of leaves         :   37 ( 294 expanded)
%              Depth                    :   20
%              Number of atoms          : 2055 (12584 expanded)
%              Number of equality atoms :  142 ( 744 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k1_tops_1 @ X42 @ X41 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ X35 ) @ ( k1_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X30 @ X28 )
        = ( k9_subset_1 @ X29 @ X30 @ ( k3_subset_1 @ X29 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('71',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_pre_topc @ X38 @ X37 )
      | ( ( k1_tops_1 @ X37 @ X38 )
        = X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('82',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( v3_pre_topc @ X38 @ X37 )
        | ( ( k1_tops_1 @ X37 @ X38 )
          = X38 ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( v3_pre_topc @ X38 @ X37 )
        | ( ( k1_tops_1 @ X37 @ X38 )
          = X38 ) ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 ) )
   <= ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(split,[status(esa)],['81'])).

thf('85',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ~ ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
        | ~ ( v3_pre_topc @ X38 @ X37 )
        | ( ( k1_tops_1 @ X37 @ X38 )
          = X38 ) )
    | ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(split,[status(esa)],['81'])).

thf('90',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_pre_topc @ X38 @ X37 )
      | ( ( k1_tops_1 @ X37 @ X38 )
        = X38 ) ) ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_pre_topc @ X38 @ X37 )
      | ( ( k1_tops_1 @ X37 @ X38 )
        = X38 ) ) ),
    inference(simpl_trail,[status(thm)],['82','90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','94'])).

thf('96',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('97',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['77'])).

thf('99',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('102',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['78','100','101'])).

thf('103',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['76','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('105',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','74','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('108',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','68','110'])).

thf('112',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','111'])).

thf('113',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('115',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','18','19'])).

thf('119',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','18','19'])).

thf('120',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('122',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','18','19'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('127',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('129',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','129'])).

thf('131',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('132',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('133',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('137',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('138',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
       != X39 )
      | ( v3_pre_topc @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('143',plain,
    ( ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 )
        | ( ( k1_tops_1 @ X40 @ X39 )
         != X39 )
        | ( v3_pre_topc @ X39 @ X40 ) )
   <= ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 )
        | ( ( k1_tops_1 @ X40 @ X39 )
         != X39 )
        | ( v3_pre_topc @ X39 @ X40 ) ) ),
    inference(split,[status(esa)],['142'])).

thf('144',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(split,[status(esa)],['142'])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ~ ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ! [X39: $i,X40: $i] :
        ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v2_pre_topc @ X40 )
        | ( ( k1_tops_1 @ X40 @ X39 )
         != X39 )
        | ( v3_pre_topc @ X39 @ X40 ) )
    | ! [X37: $i,X38: $i] :
        ( ~ ( l1_pre_topc @ X37 )
        | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(split,[status(esa)],['142'])).

thf('150',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( ( k1_tops_1 @ X40 @ X39 )
       != X39 )
      | ( v3_pre_topc @ X39 @ X40 ) ) ),
    inference('sat_resolution*',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( ( k1_tops_1 @ X40 @ X39 )
       != X39 )
      | ( v3_pre_topc @ X39 @ X40 ) ) ),
    inference(simpl_trail,[status(thm)],['143','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','151'])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
       != ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( v3_pre_topc @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['138','159'])).

thf('161',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('162',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('163',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('165',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['78','100'])).

thf('166',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['164','165'])).

thf('167',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['163','166'])).

thf('168',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['137','167'])).

thf('169',plain,(
    ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['130','168'])).

thf('170',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9UjVz7QfSr
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.91/2.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.91/2.15  % Solved by: fo/fo7.sh
% 1.91/2.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.15  % done 4283 iterations in 1.690s
% 1.91/2.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.91/2.15  % SZS output start Refutation
% 1.91/2.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.91/2.15  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.91/2.15  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.91/2.15  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.91/2.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.91/2.15  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.91/2.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.91/2.15  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.91/2.15  thf(sk_B_type, type, sk_B: $i).
% 1.91/2.15  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.91/2.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.91/2.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.91/2.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.91/2.15  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.91/2.15  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.91/2.15  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.91/2.15  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.91/2.15  thf(t76_tops_1, conjecture,
% 1.91/2.15    (![A:$i]:
% 1.91/2.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.15       ( ![B:$i]:
% 1.91/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.15           ( ( v3_pre_topc @ B @ A ) <=>
% 1.91/2.15             ( ( k2_tops_1 @ A @ B ) =
% 1.91/2.15               ( k7_subset_1 @
% 1.91/2.15                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.91/2.15  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.15    (~( ![A:$i]:
% 1.91/2.15        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.15          ( ![B:$i]:
% 1.91/2.15            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.15              ( ( v3_pre_topc @ B @ A ) <=>
% 1.91/2.15                ( ( k2_tops_1 @ A @ B ) =
% 1.91/2.15                  ( k7_subset_1 @
% 1.91/2.15                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.91/2.15    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.91/2.15  thf('0', plain,
% 1.91/2.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf(t74_tops_1, axiom,
% 1.91/2.15    (![A:$i]:
% 1.91/2.15     ( ( l1_pre_topc @ A ) =>
% 1.91/2.15       ( ![B:$i]:
% 1.91/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.15           ( ( k1_tops_1 @ A @ B ) =
% 1.91/2.15             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.91/2.15  thf('1', plain,
% 1.91/2.15      (![X41 : $i, X42 : $i]:
% 1.91/2.15         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.91/2.15          | ((k1_tops_1 @ X42 @ X41)
% 1.91/2.15              = (k7_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 1.91/2.15                 (k2_tops_1 @ X42 @ X41)))
% 1.91/2.15          | ~ (l1_pre_topc @ X42))),
% 1.91/2.15      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.91/2.15  thf('2', plain,
% 1.91/2.15      ((~ (l1_pre_topc @ sk_A)
% 1.91/2.15        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.91/2.15            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.91/2.15               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.91/2.15      inference('sup-', [status(thm)], ['0', '1'])).
% 1.91/2.15  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf('4', plain,
% 1.91/2.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf(redefinition_k7_subset_1, axiom,
% 1.91/2.15    (![A:$i,B:$i,C:$i]:
% 1.91/2.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.15       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.91/2.15  thf('5', plain,
% 1.91/2.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.91/2.15         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.91/2.15          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.91/2.15      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.91/2.15  thf('6', plain,
% 1.91/2.15      (![X0 : $i]:
% 1.91/2.15         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.91/2.15           = (k4_xboole_0 @ sk_B @ X0))),
% 1.91/2.15      inference('sup-', [status(thm)], ['4', '5'])).
% 1.91/2.15  thf('7', plain,
% 1.91/2.15      (((k1_tops_1 @ sk_A @ sk_B)
% 1.91/2.15         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.15      inference('demod', [status(thm)], ['2', '3', '6'])).
% 1.91/2.15  thf(t36_xboole_1, axiom,
% 1.91/2.15    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.91/2.15  thf('8', plain,
% 1.91/2.15      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.91/2.15      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.91/2.15  thf(t28_xboole_1, axiom,
% 1.91/2.15    (![A:$i,B:$i]:
% 1.91/2.15     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.91/2.15  thf('9', plain,
% 1.91/2.15      (![X10 : $i, X11 : $i]:
% 1.91/2.15         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.91/2.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.91/2.15  thf('10', plain,
% 1.91/2.15      (![X0 : $i, X1 : $i]:
% 1.91/2.15         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.91/2.15           = (k4_xboole_0 @ X0 @ X1))),
% 1.91/2.15      inference('sup-', [status(thm)], ['8', '9'])).
% 1.91/2.15  thf(commutativity_k3_xboole_0, axiom,
% 1.91/2.15    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.91/2.15  thf('11', plain,
% 1.91/2.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.91/2.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.91/2.15  thf('12', plain,
% 1.91/2.15      (![X0 : $i, X1 : $i]:
% 1.91/2.15         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.91/2.15           = (k4_xboole_0 @ X0 @ X1))),
% 1.91/2.15      inference('demod', [status(thm)], ['10', '11'])).
% 1.91/2.15  thf(t100_xboole_1, axiom,
% 1.91/2.15    (![A:$i,B:$i]:
% 1.91/2.15     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.91/2.15  thf('13', plain,
% 1.91/2.15      (![X8 : $i, X9 : $i]:
% 1.91/2.15         ((k4_xboole_0 @ X8 @ X9)
% 1.91/2.15           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.91/2.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.91/2.15  thf('14', plain,
% 1.91/2.15      (![X0 : $i, X1 : $i]:
% 1.91/2.15         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.91/2.15           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.91/2.15      inference('sup+', [status(thm)], ['12', '13'])).
% 1.91/2.15  thf('15', plain,
% 1.91/2.15      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.91/2.15         = (k5_xboole_0 @ sk_B @ 
% 1.91/2.15            (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.91/2.15      inference('sup+', [status(thm)], ['7', '14'])).
% 1.91/2.15  thf('16', plain,
% 1.91/2.15      (((k1_tops_1 @ sk_A @ sk_B)
% 1.91/2.15         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.15      inference('demod', [status(thm)], ['2', '3', '6'])).
% 1.91/2.15  thf(t48_xboole_1, axiom,
% 1.91/2.15    (![A:$i,B:$i]:
% 1.91/2.15     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.91/2.15  thf('17', plain,
% 1.91/2.15      (![X15 : $i, X16 : $i]:
% 1.91/2.15         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.91/2.15           = (k3_xboole_0 @ X15 @ X16))),
% 1.91/2.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.15  thf('18', plain,
% 1.91/2.15      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.91/2.15         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.15      inference('sup+', [status(thm)], ['16', '17'])).
% 1.91/2.15  thf('19', plain,
% 1.91/2.15      (((k1_tops_1 @ sk_A @ sk_B)
% 1.91/2.15         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.15      inference('demod', [status(thm)], ['2', '3', '6'])).
% 1.91/2.15  thf('20', plain,
% 1.91/2.15      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.91/2.15         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.15      inference('demod', [status(thm)], ['15', '18', '19'])).
% 1.91/2.15  thf('21', plain,
% 1.91/2.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf(l78_tops_1, axiom,
% 1.91/2.15    (![A:$i]:
% 1.91/2.15     ( ( l1_pre_topc @ A ) =>
% 1.91/2.15       ( ![B:$i]:
% 1.91/2.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.15           ( ( k2_tops_1 @ A @ B ) =
% 1.91/2.15             ( k7_subset_1 @
% 1.91/2.15               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.91/2.15               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.91/2.15  thf('22', plain,
% 1.91/2.15      (![X35 : $i, X36 : $i]:
% 1.91/2.15         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.91/2.15          | ((k2_tops_1 @ X36 @ X35)
% 1.91/2.15              = (k7_subset_1 @ (u1_struct_0 @ X36) @ 
% 1.91/2.15                 (k2_pre_topc @ X36 @ X35) @ (k1_tops_1 @ X36 @ X35)))
% 1.91/2.15          | ~ (l1_pre_topc @ X36))),
% 1.91/2.15      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.91/2.15  thf('23', plain,
% 1.91/2.15      ((~ (l1_pre_topc @ sk_A)
% 1.91/2.15        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.15            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.15               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.91/2.15      inference('sup-', [status(thm)], ['21', '22'])).
% 1.91/2.15  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf('25', plain,
% 1.91/2.15      (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.15         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.15            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.15      inference('demod', [status(thm)], ['23', '24'])).
% 1.91/2.15  thf('26', plain,
% 1.91/2.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf(dt_k2_pre_topc, axiom,
% 1.91/2.15    (![A:$i,B:$i]:
% 1.91/2.15     ( ( ( l1_pre_topc @ A ) & 
% 1.91/2.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.91/2.15       ( m1_subset_1 @
% 1.91/2.15         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.91/2.15  thf('27', plain,
% 1.91/2.15      (![X33 : $i, X34 : $i]:
% 1.91/2.15         (~ (l1_pre_topc @ X33)
% 1.91/2.15          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.91/2.15          | (m1_subset_1 @ (k2_pre_topc @ X33 @ X34) @ 
% 1.91/2.15             (k1_zfmisc_1 @ (u1_struct_0 @ X33))))),
% 1.91/2.15      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.91/2.15  thf('28', plain,
% 1.91/2.15      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.15         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.15        | ~ (l1_pre_topc @ sk_A))),
% 1.91/2.15      inference('sup-', [status(thm)], ['26', '27'])).
% 1.91/2.15  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf('30', plain,
% 1.91/2.15      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('demod', [status(thm)], ['28', '29'])).
% 1.91/2.15  thf(dt_k7_subset_1, axiom,
% 1.91/2.15    (![A:$i,B:$i,C:$i]:
% 1.91/2.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.15       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.91/2.15  thf('31', plain,
% 1.91/2.15      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.91/2.15         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.91/2.15          | (m1_subset_1 @ (k7_subset_1 @ X20 @ X19 @ X21) @ 
% 1.91/2.15             (k1_zfmisc_1 @ X20)))),
% 1.91/2.15      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.91/2.15  thf('32', plain,
% 1.91/2.15      (![X0 : $i]:
% 1.91/2.15         (m1_subset_1 @ 
% 1.91/2.15          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.15           X0) @ 
% 1.91/2.15          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('sup-', [status(thm)], ['30', '31'])).
% 1.91/2.15  thf('33', plain,
% 1.91/2.15      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.91/2.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('sup+', [status(thm)], ['25', '32'])).
% 1.91/2.15  thf('34', plain,
% 1.91/2.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.15  thf(t32_subset_1, axiom,
% 1.91/2.15    (![A:$i,B:$i]:
% 1.91/2.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.15       ( ![C:$i]:
% 1.91/2.15         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.15           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.91/2.15             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.91/2.15  thf('35', plain,
% 1.91/2.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.91/2.15         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.91/2.15          | ((k7_subset_1 @ X29 @ X30 @ X28)
% 1.91/2.15              = (k9_subset_1 @ X29 @ X30 @ (k3_subset_1 @ X29 @ X28)))
% 1.91/2.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.91/2.15      inference('cnf', [status(esa)], [t32_subset_1])).
% 1.91/2.15  thf('36', plain,
% 1.91/2.15      (![X0 : $i]:
% 1.91/2.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.15          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.91/2.16              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.91/2.16                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.91/2.16      inference('sup-', [status(thm)], ['34', '35'])).
% 1.91/2.16  thf('37', plain,
% 1.91/2.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf(dt_k3_subset_1, axiom,
% 1.91/2.16    (![A:$i,B:$i]:
% 1.91/2.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.16       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.91/2.16  thf('38', plain,
% 1.91/2.16      (![X17 : $i, X18 : $i]:
% 1.91/2.16         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 1.91/2.16          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.91/2.16      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.91/2.16  thf('39', plain,
% 1.91/2.16      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.91/2.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['37', '38'])).
% 1.91/2.16  thf(redefinition_k9_subset_1, axiom,
% 1.91/2.16    (![A:$i,B:$i,C:$i]:
% 1.91/2.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.16       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.91/2.16  thf('40', plain,
% 1.91/2.16      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.91/2.16         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 1.91/2.16          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.91/2.16      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.91/2.16  thf('41', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.91/2.16           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.91/2.16           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['39', '40'])).
% 1.91/2.16  thf('42', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.16          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.91/2.16              = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.91/2.16      inference('demod', [status(thm)], ['36', '41'])).
% 1.91/2.16  thf('43', plain,
% 1.91/2.16      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.91/2.16         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.91/2.16            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['33', '42'])).
% 1.91/2.16  thf('44', plain,
% 1.91/2.16      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.91/2.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['25', '32'])).
% 1.91/2.16  thf('45', plain,
% 1.91/2.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.91/2.16         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.91/2.16          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.91/2.16      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.91/2.16  thf('46', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.91/2.16           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['44', '45'])).
% 1.91/2.16  thf('47', plain,
% 1.91/2.16      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.91/2.16         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.91/2.16            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['43', '46'])).
% 1.91/2.16  thf('48', plain,
% 1.91/2.16      (![X15 : $i, X16 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.91/2.16           = (k3_xboole_0 @ X15 @ X16))),
% 1.91/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.16  thf('49', plain,
% 1.91/2.16      (![X15 : $i, X16 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.91/2.16           = (k3_xboole_0 @ X15 @ X16))),
% 1.91/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.16  thf('50', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['48', '49'])).
% 1.91/2.16  thf('51', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.91/2.16           = (k4_xboole_0 @ X0 @ X1))),
% 1.91/2.16      inference('demod', [status(thm)], ['10', '11'])).
% 1.91/2.16  thf('52', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k4_xboole_0 @ X1 @ X0))),
% 1.91/2.16      inference('demod', [status(thm)], ['50', '51'])).
% 1.91/2.16  thf('53', plain,
% 1.91/2.16      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.91/2.16         (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.91/2.16         = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.91/2.16            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['47', '52'])).
% 1.91/2.16  thf('54', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.91/2.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.91/2.16  thf('55', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k4_xboole_0 @ X1 @ X0))),
% 1.91/2.16      inference('demod', [status(thm)], ['50', '51'])).
% 1.91/2.16  thf('56', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k4_xboole_0 @ X0 @ X1))),
% 1.91/2.16      inference('sup+', [status(thm)], ['54', '55'])).
% 1.91/2.16  thf('57', plain,
% 1.91/2.16      (![X15 : $i, X16 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.91/2.16           = (k3_xboole_0 @ X15 @ X16))),
% 1.91/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.16  thf('58', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['56', '57'])).
% 1.91/2.16  thf('59', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.91/2.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.91/2.16  thf('60', plain,
% 1.91/2.16      (![X15 : $i, X16 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.91/2.16           = (k3_xboole_0 @ X15 @ X16))),
% 1.91/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.16  thf('61', plain,
% 1.91/2.16      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.91/2.16      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.91/2.16  thf('62', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.91/2.16      inference('sup+', [status(thm)], ['60', '61'])).
% 1.91/2.16  thf('63', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.91/2.16      inference('sup+', [status(thm)], ['59', '62'])).
% 1.91/2.16  thf('64', plain,
% 1.91/2.16      (![X10 : $i, X11 : $i]:
% 1.91/2.16         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.91/2.16      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.91/2.16  thf('65', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.91/2.16           = (k3_xboole_0 @ X1 @ X0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['63', '64'])).
% 1.91/2.16  thf('66', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.91/2.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.91/2.16  thf('67', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k3_xboole_0 @ X1 @ X0))),
% 1.91/2.16      inference('demod', [status(thm)], ['65', '66'])).
% 1.91/2.16  thf('68', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k3_xboole_0 @ X0 @ X1))),
% 1.91/2.16      inference('demod', [status(thm)], ['58', '67'])).
% 1.91/2.16  thf('69', plain,
% 1.91/2.16      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('demod', [status(thm)], ['28', '29'])).
% 1.91/2.16  thf('70', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.16          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.91/2.16              = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.91/2.16      inference('demod', [status(thm)], ['36', '41'])).
% 1.91/2.16  thf('71', plain,
% 1.91/2.16      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16         sk_B)
% 1.91/2.16         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['69', '70'])).
% 1.91/2.16  thf('72', plain,
% 1.91/2.16      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('demod', [status(thm)], ['28', '29'])).
% 1.91/2.16  thf('73', plain,
% 1.91/2.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.91/2.16         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.91/2.16          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 1.91/2.16      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.91/2.16  thf('74', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['72', '73'])).
% 1.91/2.16  thf('75', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.91/2.16        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('76', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.91/2.16         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.91/2.16      inference('split', [status(esa)], ['75'])).
% 1.91/2.16  thf('77', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.91/2.16        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('78', plain,
% 1.91/2.16      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 1.91/2.16       ~
% 1.91/2.16       (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.91/2.16      inference('split', [status(esa)], ['77'])).
% 1.91/2.16  thf('79', plain,
% 1.91/2.16      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.91/2.16      inference('split', [status(esa)], ['75'])).
% 1.91/2.16  thf('80', plain,
% 1.91/2.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf(t55_tops_1, axiom,
% 1.91/2.16    (![A:$i]:
% 1.91/2.16     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.16       ( ![B:$i]:
% 1.91/2.16         ( ( l1_pre_topc @ B ) =>
% 1.91/2.16           ( ![C:$i]:
% 1.91/2.16             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.16               ( ![D:$i]:
% 1.91/2.16                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.91/2.16                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.91/2.16                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.91/2.16                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.91/2.16                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.16  thf('81', plain,
% 1.91/2.16      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.91/2.16         (~ (l1_pre_topc @ X37)
% 1.91/2.16          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.91/2.16          | ~ (v3_pre_topc @ X38 @ X37)
% 1.91/2.16          | ((k1_tops_1 @ X37 @ X38) = (X38))
% 1.91/2.16          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16          | ~ (l1_pre_topc @ X40)
% 1.91/2.16          | ~ (v2_pre_topc @ X40))),
% 1.91/2.16      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.91/2.16  thf('82', plain,
% 1.91/2.16      ((![X37 : $i, X38 : $i]:
% 1.91/2.16          (~ (l1_pre_topc @ X37)
% 1.91/2.16           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.91/2.16           | ~ (v3_pre_topc @ X38 @ X37)
% 1.91/2.16           | ((k1_tops_1 @ X37 @ X38) = (X38))))
% 1.91/2.16         <= ((![X37 : $i, X38 : $i]:
% 1.91/2.16                (~ (l1_pre_topc @ X37)
% 1.91/2.16                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.91/2.16                 | ~ (v3_pre_topc @ X38 @ X37)
% 1.91/2.16                 | ((k1_tops_1 @ X37 @ X38) = (X38)))))),
% 1.91/2.16      inference('split', [status(esa)], ['81'])).
% 1.91/2.16  thf('83', plain,
% 1.91/2.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('84', plain,
% 1.91/2.16      ((![X39 : $i, X40 : $i]:
% 1.91/2.16          (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16           | ~ (l1_pre_topc @ X40)
% 1.91/2.16           | ~ (v2_pre_topc @ X40)))
% 1.91/2.16         <= ((![X39 : $i, X40 : $i]:
% 1.91/2.16                (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16                 | ~ (l1_pre_topc @ X40)
% 1.91/2.16                 | ~ (v2_pre_topc @ X40))))),
% 1.91/2.16      inference('split', [status(esa)], ['81'])).
% 1.91/2.16  thf('85', plain,
% 1.91/2.16      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 1.91/2.16         <= ((![X39 : $i, X40 : $i]:
% 1.91/2.16                (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16                 | ~ (l1_pre_topc @ X40)
% 1.91/2.16                 | ~ (v2_pre_topc @ X40))))),
% 1.91/2.16      inference('sup-', [status(thm)], ['83', '84'])).
% 1.91/2.16  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('88', plain,
% 1.91/2.16      (~
% 1.91/2.16       (![X39 : $i, X40 : $i]:
% 1.91/2.16          (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16           | ~ (l1_pre_topc @ X40)
% 1.91/2.16           | ~ (v2_pre_topc @ X40)))),
% 1.91/2.16      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.91/2.16  thf('89', plain,
% 1.91/2.16      ((![X37 : $i, X38 : $i]:
% 1.91/2.16          (~ (l1_pre_topc @ X37)
% 1.91/2.16           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.91/2.16           | ~ (v3_pre_topc @ X38 @ X37)
% 1.91/2.16           | ((k1_tops_1 @ X37 @ X38) = (X38)))) | 
% 1.91/2.16       (![X39 : $i, X40 : $i]:
% 1.91/2.16          (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16           | ~ (l1_pre_topc @ X40)
% 1.91/2.16           | ~ (v2_pre_topc @ X40)))),
% 1.91/2.16      inference('split', [status(esa)], ['81'])).
% 1.91/2.16  thf('90', plain,
% 1.91/2.16      ((![X37 : $i, X38 : $i]:
% 1.91/2.16          (~ (l1_pre_topc @ X37)
% 1.91/2.16           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.91/2.16           | ~ (v3_pre_topc @ X38 @ X37)
% 1.91/2.16           | ((k1_tops_1 @ X37 @ X38) = (X38))))),
% 1.91/2.16      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 1.91/2.16  thf('91', plain,
% 1.91/2.16      (![X37 : $i, X38 : $i]:
% 1.91/2.16         (~ (l1_pre_topc @ X37)
% 1.91/2.16          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.91/2.16          | ~ (v3_pre_topc @ X38 @ X37)
% 1.91/2.16          | ((k1_tops_1 @ X37 @ X38) = (X38)))),
% 1.91/2.16      inference('simpl_trail', [status(thm)], ['82', '90'])).
% 1.91/2.16  thf('92', plain,
% 1.91/2.16      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 1.91/2.16        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 1.91/2.16        | ~ (l1_pre_topc @ sk_A))),
% 1.91/2.16      inference('sup-', [status(thm)], ['80', '91'])).
% 1.91/2.16  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('94', plain,
% 1.91/2.16      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.91/2.16      inference('demod', [status(thm)], ['92', '93'])).
% 1.91/2.16  thf('95', plain,
% 1.91/2.16      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.91/2.16         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['79', '94'])).
% 1.91/2.16  thf('96', plain,
% 1.91/2.16      (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['23', '24'])).
% 1.91/2.16  thf('97', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.91/2.16         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['95', '96'])).
% 1.91/2.16  thf('98', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.91/2.16         <= (~
% 1.91/2.16             (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.91/2.16      inference('split', [status(esa)], ['77'])).
% 1.91/2.16  thf('99', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         <= (~
% 1.91/2.16             (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.91/2.16             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['97', '98'])).
% 1.91/2.16  thf('100', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.91/2.16       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.91/2.16      inference('simplify', [status(thm)], ['99'])).
% 1.91/2.16  thf('101', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.91/2.16       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.91/2.16      inference('split', [status(esa)], ['75'])).
% 1.91/2.16  thf('102', plain,
% 1.91/2.16      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.91/2.16             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.91/2.16      inference('sat_resolution*', [status(thm)], ['78', '100', '101'])).
% 1.91/2.16  thf('103', plain,
% 1.91/2.16      (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16            sk_B))),
% 1.91/2.16      inference('simpl_trail', [status(thm)], ['76', '102'])).
% 1.91/2.16  thf('104', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['72', '73'])).
% 1.91/2.16  thf('105', plain,
% 1.91/2.16      (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 1.91/2.16      inference('demod', [status(thm)], ['103', '104'])).
% 1.91/2.16  thf('106', plain,
% 1.91/2.16      (((k2_tops_1 @ sk_A @ sk_B)
% 1.91/2.16         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.91/2.16            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['71', '74', '105'])).
% 1.91/2.16  thf('107', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.91/2.16      inference('sup+', [status(thm)], ['59', '62'])).
% 1.91/2.16  thf(l32_xboole_1, axiom,
% 1.91/2.16    (![A:$i,B:$i]:
% 1.91/2.16     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.91/2.16  thf('108', plain,
% 1.91/2.16      (![X5 : $i, X7 : $i]:
% 1.91/2.16         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.91/2.16      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.91/2.16  thf('109', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['107', '108'])).
% 1.91/2.16  thf('110', plain,
% 1.91/2.16      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.91/2.16         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (k1_xboole_0))),
% 1.91/2.16      inference('sup+', [status(thm)], ['106', '109'])).
% 1.91/2.16  thf('111', plain,
% 1.91/2.16      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.91/2.16      inference('demod', [status(thm)], ['53', '68', '110'])).
% 1.91/2.16  thf('112', plain,
% 1.91/2.16      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.91/2.16      inference('sup+', [status(thm)], ['20', '111'])).
% 1.91/2.16  thf('113', plain,
% 1.91/2.16      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.91/2.16         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['16', '17'])).
% 1.91/2.16  thf('114', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.91/2.16           = (k4_xboole_0 @ X0 @ X1))),
% 1.91/2.16      inference('demod', [status(thm)], ['10', '11'])).
% 1.91/2.16  thf('115', plain,
% 1.91/2.16      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['113', '114'])).
% 1.91/2.16  thf('116', plain,
% 1.91/2.16      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.91/2.16         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['16', '17'])).
% 1.91/2.16  thf('117', plain,
% 1.91/2.16      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['115', '116'])).
% 1.91/2.16  thf('118', plain,
% 1.91/2.16      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.91/2.16         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['15', '18', '19'])).
% 1.91/2.16  thf('119', plain,
% 1.91/2.16      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.91/2.16         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['15', '18', '19'])).
% 1.91/2.16  thf('120', plain,
% 1.91/2.16      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.91/2.16  thf('121', plain,
% 1.91/2.16      (![X15 : $i, X16 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.91/2.16           = (k3_xboole_0 @ X15 @ X16))),
% 1.91/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.91/2.16  thf('122', plain,
% 1.91/2.16      (![X5 : $i, X6 : $i]:
% 1.91/2.16         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.91/2.16      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.91/2.16  thf('123', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.91/2.16          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['121', '122'])).
% 1.91/2.16  thf('124', plain,
% 1.91/2.16      ((((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))
% 1.91/2.16        | (r1_tarski @ sk_B @ 
% 1.91/2.16           (k4_xboole_0 @ sk_B @ 
% 1.91/2.16            (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.91/2.16      inference('sup-', [status(thm)], ['120', '123'])).
% 1.91/2.16  thf('125', plain,
% 1.91/2.16      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.91/2.16         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['15', '18', '19'])).
% 1.91/2.16  thf('126', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.91/2.16           = (k4_xboole_0 @ X1 @ X0))),
% 1.91/2.16      inference('demod', [status(thm)], ['50', '51'])).
% 1.91/2.16  thf('127', plain,
% 1.91/2.16      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('sup+', [status(thm)], ['125', '126'])).
% 1.91/2.16  thf('128', plain,
% 1.91/2.16      (((k1_tops_1 @ sk_A @ sk_B)
% 1.91/2.16         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['2', '3', '6'])).
% 1.91/2.16  thf('129', plain,
% 1.91/2.16      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.91/2.16      inference('demod', [status(thm)], ['127', '128'])).
% 1.91/2.16  thf('130', plain,
% 1.91/2.16      ((((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))
% 1.91/2.16        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['124', '129'])).
% 1.91/2.16  thf('131', plain,
% 1.91/2.16      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.91/2.16      inference('demod', [status(thm)], ['127', '128'])).
% 1.91/2.16  thf('132', plain,
% 1.91/2.16      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.91/2.16      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.91/2.16  thf(d10_xboole_0, axiom,
% 1.91/2.16    (![A:$i,B:$i]:
% 1.91/2.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.16  thf('133', plain,
% 1.91/2.16      (![X2 : $i, X4 : $i]:
% 1.91/2.16         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.91/2.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.91/2.16  thf('134', plain,
% 1.91/2.16      (![X0 : $i, X1 : $i]:
% 1.91/2.16         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.91/2.16          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['132', '133'])).
% 1.91/2.16  thf('135', plain,
% 1.91/2.16      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.91/2.16        | ((sk_B)
% 1.91/2.16            = (k4_xboole_0 @ sk_B @ 
% 1.91/2.16               (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.91/2.16      inference('sup-', [status(thm)], ['131', '134'])).
% 1.91/2.16  thf('136', plain,
% 1.91/2.16      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.91/2.16         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.91/2.16      inference('demod', [status(thm)], ['127', '128'])).
% 1.91/2.16  thf('137', plain,
% 1.91/2.16      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.91/2.16        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 1.91/2.16      inference('demod', [status(thm)], ['135', '136'])).
% 1.91/2.16  thf(t3_boole, axiom,
% 1.91/2.16    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.91/2.16  thf('138', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.91/2.16      inference('cnf', [status(esa)], [t3_boole])).
% 1.91/2.16  thf('139', plain,
% 1.91/2.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('140', plain,
% 1.91/2.16      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.91/2.16         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.91/2.16          | (m1_subset_1 @ (k7_subset_1 @ X20 @ X19 @ X21) @ 
% 1.91/2.16             (k1_zfmisc_1 @ X20)))),
% 1.91/2.16      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.91/2.16  thf('141', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.91/2.16          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('sup-', [status(thm)], ['139', '140'])).
% 1.91/2.16  thf('142', plain,
% 1.91/2.16      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.91/2.16         (~ (l1_pre_topc @ X37)
% 1.91/2.16          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.91/2.16          | ((k1_tops_1 @ X40 @ X39) != (X39))
% 1.91/2.16          | (v3_pre_topc @ X39 @ X40)
% 1.91/2.16          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16          | ~ (l1_pre_topc @ X40)
% 1.91/2.16          | ~ (v2_pre_topc @ X40))),
% 1.91/2.16      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.91/2.16  thf('143', plain,
% 1.91/2.16      ((![X39 : $i, X40 : $i]:
% 1.91/2.16          (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16           | ~ (l1_pre_topc @ X40)
% 1.91/2.16           | ~ (v2_pre_topc @ X40)
% 1.91/2.16           | ((k1_tops_1 @ X40 @ X39) != (X39))
% 1.91/2.16           | (v3_pre_topc @ X39 @ X40)))
% 1.91/2.16         <= ((![X39 : $i, X40 : $i]:
% 1.91/2.16                (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16                 | ~ (l1_pre_topc @ X40)
% 1.91/2.16                 | ~ (v2_pre_topc @ X40)
% 1.91/2.16                 | ((k1_tops_1 @ X40 @ X39) != (X39))
% 1.91/2.16                 | (v3_pre_topc @ X39 @ X40))))),
% 1.91/2.16      inference('split', [status(esa)], ['142'])).
% 1.91/2.16  thf('144', plain,
% 1.91/2.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('145', plain,
% 1.91/2.16      ((![X37 : $i, X38 : $i]:
% 1.91/2.16          (~ (l1_pre_topc @ X37)
% 1.91/2.16           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))))
% 1.91/2.16         <= ((![X37 : $i, X38 : $i]:
% 1.91/2.16                (~ (l1_pre_topc @ X37)
% 1.91/2.16                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37))))))),
% 1.91/2.16      inference('split', [status(esa)], ['142'])).
% 1.91/2.16  thf('146', plain,
% 1.91/2.16      ((~ (l1_pre_topc @ sk_A))
% 1.91/2.16         <= ((![X37 : $i, X38 : $i]:
% 1.91/2.16                (~ (l1_pre_topc @ X37)
% 1.91/2.16                 | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37))))))),
% 1.91/2.16      inference('sup-', [status(thm)], ['144', '145'])).
% 1.91/2.16  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('148', plain,
% 1.91/2.16      (~
% 1.91/2.16       (![X37 : $i, X38 : $i]:
% 1.91/2.16          (~ (l1_pre_topc @ X37)
% 1.91/2.16           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))))),
% 1.91/2.16      inference('demod', [status(thm)], ['146', '147'])).
% 1.91/2.16  thf('149', plain,
% 1.91/2.16      ((![X39 : $i, X40 : $i]:
% 1.91/2.16          (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16           | ~ (l1_pre_topc @ X40)
% 1.91/2.16           | ~ (v2_pre_topc @ X40)
% 1.91/2.16           | ((k1_tops_1 @ X40 @ X39) != (X39))
% 1.91/2.16           | (v3_pre_topc @ X39 @ X40))) | 
% 1.91/2.16       (![X37 : $i, X38 : $i]:
% 1.91/2.16          (~ (l1_pre_topc @ X37)
% 1.91/2.16           | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))))),
% 1.91/2.16      inference('split', [status(esa)], ['142'])).
% 1.91/2.16  thf('150', plain,
% 1.91/2.16      ((![X39 : $i, X40 : $i]:
% 1.91/2.16          (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16           | ~ (l1_pre_topc @ X40)
% 1.91/2.16           | ~ (v2_pre_topc @ X40)
% 1.91/2.16           | ((k1_tops_1 @ X40 @ X39) != (X39))
% 1.91/2.16           | (v3_pre_topc @ X39 @ X40)))),
% 1.91/2.16      inference('sat_resolution*', [status(thm)], ['148', '149'])).
% 1.91/2.16  thf('151', plain,
% 1.91/2.16      (![X39 : $i, X40 : $i]:
% 1.91/2.16         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.91/2.16          | ~ (l1_pre_topc @ X40)
% 1.91/2.16          | ~ (v2_pre_topc @ X40)
% 1.91/2.16          | ((k1_tops_1 @ X40 @ X39) != (X39))
% 1.91/2.16          | (v3_pre_topc @ X39 @ X40))),
% 1.91/2.16      inference('simpl_trail', [status(thm)], ['143', '150'])).
% 1.91/2.16  thf('152', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((v3_pre_topc @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.91/2.16           sk_A)
% 1.91/2.16          | ((k1_tops_1 @ sk_A @ 
% 1.91/2.16              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 1.91/2.16              != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 1.91/2.16          | ~ (v2_pre_topc @ sk_A)
% 1.91/2.16          | ~ (l1_pre_topc @ sk_A))),
% 1.91/2.16      inference('sup-', [status(thm)], ['141', '151'])).
% 1.91/2.16  thf('153', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.16  thf('155', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((v3_pre_topc @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.91/2.16           sk_A)
% 1.91/2.16          | ((k1_tops_1 @ sk_A @ 
% 1.91/2.16              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 1.91/2.16              != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)))),
% 1.91/2.16      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.91/2.16  thf('156', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.91/2.16           = (k4_xboole_0 @ sk_B @ X0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['4', '5'])).
% 1.91/2.16  thf('157', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.91/2.16           = (k4_xboole_0 @ sk_B @ X0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['4', '5'])).
% 1.91/2.16  thf('158', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.91/2.16           = (k4_xboole_0 @ sk_B @ X0))),
% 1.91/2.16      inference('sup-', [status(thm)], ['4', '5'])).
% 1.91/2.16  thf('159', plain,
% 1.91/2.16      (![X0 : $i]:
% 1.91/2.16         ((v3_pre_topc @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.91/2.16          | ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 1.91/2.16              != (k4_xboole_0 @ sk_B @ X0)))),
% 1.91/2.16      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 1.91/2.16  thf('160', plain,
% 1.91/2.16      ((((k1_tops_1 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_B @ k1_xboole_0))
% 1.91/2.16        | (v3_pre_topc @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ sk_A))),
% 1.91/2.16      inference('sup-', [status(thm)], ['138', '159'])).
% 1.91/2.16  thf('161', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.91/2.16      inference('cnf', [status(esa)], [t3_boole])).
% 1.91/2.16  thf('162', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.91/2.16      inference('cnf', [status(esa)], [t3_boole])).
% 1.91/2.16  thf('163', plain,
% 1.91/2.16      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 1.91/2.16      inference('demod', [status(thm)], ['160', '161', '162'])).
% 1.91/2.16  thf('164', plain,
% 1.91/2.16      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.91/2.16      inference('split', [status(esa)], ['77'])).
% 1.91/2.16  thf('165', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.91/2.16      inference('sat_resolution*', [status(thm)], ['78', '100'])).
% 1.91/2.16  thf('166', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 1.91/2.16      inference('simpl_trail', [status(thm)], ['164', '165'])).
% 1.91/2.16  thf('167', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 1.91/2.16      inference('clc', [status(thm)], ['163', '166'])).
% 1.91/2.16  thf('168', plain, (~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 1.91/2.16      inference('simplify_reflect-', [status(thm)], ['137', '167'])).
% 1.91/2.16  thf('169', plain,
% 1.91/2.16      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 1.91/2.16      inference('clc', [status(thm)], ['130', '168'])).
% 1.91/2.16  thf('170', plain, ($false),
% 1.91/2.16      inference('simplify_reflect-', [status(thm)], ['112', '169'])).
% 1.91/2.16  
% 1.91/2.16  % SZS output end Refutation
% 1.91/2.16  
% 1.91/2.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
