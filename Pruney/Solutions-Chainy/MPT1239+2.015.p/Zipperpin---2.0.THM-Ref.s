%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OHe55rpODv

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:02 EST 2020

% Result     : Theorem 53.44s
% Output     : Refutation 53.44s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 489 expanded)
%              Number of leaves         :   27 ( 158 expanded)
%              Depth                    :   21
%              Number of atoms          : 1620 (5415 expanded)
%              Number of equality atoms :   32 (  73 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['27','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r1_tarski @ X35 @ X37 )
      | ( r1_tarski @ ( k1_tops_1 @ X36 @ X35 ) @ ( k1_tops_1 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C ),
    inference('sup-',[status(thm)],['52','67'])).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('78',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('82',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('88',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('90',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('94',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('98',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('105',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('111',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('133',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X16 @ X19 )
      | ~ ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['87','141'])).

thf('143',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['86','144'])).

thf('146',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['51','145'])).

thf('147',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','148'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['20','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OHe55rpODv
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:35:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 53.44/53.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 53.44/53.69  % Solved by: fo/fo7.sh
% 53.44/53.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 53.44/53.69  % done 39083 iterations in 53.215s
% 53.44/53.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 53.44/53.69  % SZS output start Refutation
% 53.44/53.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 53.44/53.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 53.44/53.69  thf(sk_C_type, type, sk_C: $i).
% 53.44/53.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 53.44/53.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 53.44/53.69  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 53.44/53.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 53.44/53.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 53.44/53.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 53.44/53.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 53.44/53.69  thf(sk_A_type, type, sk_A: $i).
% 53.44/53.69  thf(sk_B_type, type, sk_B: $i).
% 53.44/53.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 53.44/53.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 53.44/53.69  thf(t50_tops_1, conjecture,
% 53.44/53.69    (![A:$i]:
% 53.44/53.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 53.44/53.69       ( ![B:$i]:
% 53.44/53.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.44/53.69           ( ![C:$i]:
% 53.44/53.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.44/53.69               ( r1_tarski @
% 53.44/53.69                 ( k1_tops_1 @
% 53.44/53.69                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 53.44/53.69                 ( k7_subset_1 @
% 53.44/53.69                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 53.44/53.69                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 53.44/53.69  thf(zf_stmt_0, negated_conjecture,
% 53.44/53.69    (~( ![A:$i]:
% 53.44/53.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 53.44/53.69          ( ![B:$i]:
% 53.44/53.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.44/53.69              ( ![C:$i]:
% 53.44/53.69                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.44/53.69                  ( r1_tarski @
% 53.44/53.69                    ( k1_tops_1 @
% 53.44/53.69                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 53.44/53.69                    ( k7_subset_1 @
% 53.44/53.69                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 53.44/53.69                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 53.44/53.69    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 53.44/53.69  thf('0', plain,
% 53.44/53.69      (~ (r1_tarski @ 
% 53.44/53.69          (k1_tops_1 @ sk_A @ 
% 53.44/53.69           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 53.44/53.69          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 53.44/53.69           (k1_tops_1 @ sk_A @ sk_C)))),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('1', plain,
% 53.44/53.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf(redefinition_k7_subset_1, axiom,
% 53.44/53.69    (![A:$i,B:$i,C:$i]:
% 53.44/53.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 53.44/53.69       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 53.44/53.69  thf('2', plain,
% 53.44/53.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 53.44/53.69          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 53.44/53.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 53.44/53.69  thf('3', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 53.44/53.69           = (k4_xboole_0 @ sk_B @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['1', '2'])).
% 53.44/53.69  thf('4', plain,
% 53.44/53.69      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 53.44/53.69           (k1_tops_1 @ sk_A @ sk_C)))),
% 53.44/53.69      inference('demod', [status(thm)], ['0', '3'])).
% 53.44/53.69  thf('5', plain,
% 53.44/53.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf(t3_subset, axiom,
% 53.44/53.69    (![A:$i,B:$i]:
% 53.44/53.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 53.44/53.69  thf('6', plain,
% 53.44/53.69      (![X30 : $i, X31 : $i]:
% 53.44/53.69         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t3_subset])).
% 53.44/53.69  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 53.44/53.69      inference('sup-', [status(thm)], ['5', '6'])).
% 53.44/53.69  thf('8', plain,
% 53.44/53.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf(t44_tops_1, axiom,
% 53.44/53.69    (![A:$i]:
% 53.44/53.69     ( ( l1_pre_topc @ A ) =>
% 53.44/53.69       ( ![B:$i]:
% 53.44/53.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.44/53.69           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 53.44/53.69  thf('9', plain,
% 53.44/53.69      (![X33 : $i, X34 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ X34 @ X33) @ X33)
% 53.44/53.69          | ~ (l1_pre_topc @ X34))),
% 53.44/53.69      inference('cnf', [status(esa)], [t44_tops_1])).
% 53.44/53.69  thf('10', plain,
% 53.44/53.69      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 53.44/53.69      inference('sup-', [status(thm)], ['8', '9'])).
% 53.44/53.69  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 53.44/53.69      inference('demod', [status(thm)], ['10', '11'])).
% 53.44/53.69  thf(t1_xboole_1, axiom,
% 53.44/53.69    (![A:$i,B:$i,C:$i]:
% 53.44/53.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 53.44/53.69       ( r1_tarski @ A @ C ) ))).
% 53.44/53.69  thf('13', plain,
% 53.44/53.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X10 @ X11)
% 53.44/53.69          | ~ (r1_tarski @ X11 @ X12)
% 53.44/53.69          | (r1_tarski @ X10 @ X12))),
% 53.44/53.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 53.44/53.69  thf('14', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 53.44/53.69          | ~ (r1_tarski @ sk_B @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['12', '13'])).
% 53.44/53.69  thf('15', plain,
% 53.44/53.69      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 53.44/53.69      inference('sup-', [status(thm)], ['7', '14'])).
% 53.44/53.69  thf('16', plain,
% 53.44/53.69      (![X30 : $i, X32 : $i]:
% 53.44/53.69         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 53.44/53.69      inference('cnf', [status(esa)], [t3_subset])).
% 53.44/53.69  thf('17', plain,
% 53.44/53.69      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 53.44/53.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['15', '16'])).
% 53.44/53.69  thf('18', plain,
% 53.44/53.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 53.44/53.69          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 53.44/53.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 53.44/53.69  thf('19', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 53.44/53.69           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['17', '18'])).
% 53.44/53.69  thf('20', plain,
% 53.44/53.69      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 53.44/53.69      inference('demod', [status(thm)], ['4', '19'])).
% 53.44/53.69  thf('21', plain,
% 53.44/53.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('22', plain,
% 53.44/53.69      (![X33 : $i, X34 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ X34 @ X33) @ X33)
% 53.44/53.69          | ~ (l1_pre_topc @ X34))),
% 53.44/53.69      inference('cnf', [status(esa)], [t44_tops_1])).
% 53.44/53.69  thf('23', plain,
% 53.44/53.69      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 53.44/53.69      inference('sup-', [status(thm)], ['21', '22'])).
% 53.44/53.69  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('25', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 53.44/53.69      inference('demod', [status(thm)], ['23', '24'])).
% 53.44/53.69  thf(t12_xboole_1, axiom,
% 53.44/53.69    (![A:$i,B:$i]:
% 53.44/53.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 53.44/53.69  thf('26', plain,
% 53.44/53.69      (![X8 : $i, X9 : $i]:
% 53.44/53.69         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 53.44/53.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 53.44/53.69  thf('27', plain,
% 53.44/53.69      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 53.44/53.69      inference('sup-', [status(thm)], ['25', '26'])).
% 53.44/53.69  thf(d10_xboole_0, axiom,
% 53.44/53.69    (![A:$i,B:$i]:
% 53.44/53.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 53.44/53.69  thf('28', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 53.44/53.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 53.44/53.69  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 53.44/53.69      inference('simplify', [status(thm)], ['28'])).
% 53.44/53.69  thf(t109_xboole_1, axiom,
% 53.44/53.69    (![A:$i,B:$i,C:$i]:
% 53.44/53.69     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 53.44/53.69  thf('30', plain,
% 53.44/53.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k4_xboole_0 @ X5 @ X7) @ X6))),
% 53.44/53.69      inference('cnf', [status(esa)], [t109_xboole_1])).
% 53.44/53.69  thf('31', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['29', '30'])).
% 53.44/53.69  thf(t79_xboole_1, axiom,
% 53.44/53.69    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 53.44/53.69  thf('32', plain,
% 53.44/53.69      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 53.44/53.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 53.44/53.69  thf(t70_xboole_1, axiom,
% 53.44/53.69    (![A:$i,B:$i,C:$i]:
% 53.44/53.69     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 53.44/53.69            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 53.44/53.69       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 53.44/53.69            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 53.44/53.69  thf('33', plain,
% 53.44/53.69      (![X16 : $i, X17 : $i, X19 : $i]:
% 53.44/53.69         ((r1_xboole_0 @ X16 @ X17)
% 53.44/53.69          | ~ (r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X19)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t70_xboole_1])).
% 53.44/53.69  thf('34', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 53.44/53.69      inference('sup-', [status(thm)], ['32', '33'])).
% 53.44/53.69  thf(t86_xboole_1, axiom,
% 53.44/53.69    (![A:$i,B:$i,C:$i]:
% 53.44/53.69     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 53.44/53.69       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 53.44/53.69  thf('35', plain,
% 53.44/53.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X22 @ X23)
% 53.44/53.69          | ~ (r1_xboole_0 @ X22 @ X24)
% 53.44/53.69          | (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X24)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 53.44/53.69  thf('36', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.44/53.69         ((r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 53.44/53.69           (k4_xboole_0 @ X3 @ X0))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X3))),
% 53.44/53.69      inference('sup-', [status(thm)], ['34', '35'])).
% 53.44/53.69  thf('37', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)) @ 
% 53.44/53.69          (k4_xboole_0 @ X0 @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['31', '36'])).
% 53.44/53.69  thf('38', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 53.44/53.69          (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 53.44/53.69      inference('sup+', [status(thm)], ['27', '37'])).
% 53.44/53.69  thf('39', plain,
% 53.44/53.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('40', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 53.44/53.69      inference('sup-', [status(thm)], ['5', '6'])).
% 53.44/53.69  thf('41', plain,
% 53.44/53.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k4_xboole_0 @ X5 @ X7) @ X6))),
% 53.44/53.69      inference('cnf', [status(esa)], [t109_xboole_1])).
% 53.44/53.69  thf('42', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 53.44/53.69      inference('sup-', [status(thm)], ['40', '41'])).
% 53.44/53.69  thf('43', plain,
% 53.44/53.69      (![X30 : $i, X32 : $i]:
% 53.44/53.69         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 53.44/53.69      inference('cnf', [status(esa)], [t3_subset])).
% 53.44/53.69  thf('44', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 53.44/53.69          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['42', '43'])).
% 53.44/53.69  thf(t48_tops_1, axiom,
% 53.44/53.69    (![A:$i]:
% 53.44/53.69     ( ( l1_pre_topc @ A ) =>
% 53.44/53.69       ( ![B:$i]:
% 53.44/53.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.44/53.69           ( ![C:$i]:
% 53.44/53.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.44/53.69               ( ( r1_tarski @ B @ C ) =>
% 53.44/53.69                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 53.44/53.69  thf('45', plain,
% 53.44/53.69      (![X35 : $i, X36 : $i, X37 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 53.44/53.69          | ~ (r1_tarski @ X35 @ X37)
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ X36 @ X35) @ (k1_tops_1 @ X36 @ X37))
% 53.44/53.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 53.44/53.69          | ~ (l1_pre_topc @ X36))),
% 53.44/53.69      inference('cnf', [status(esa)], [t48_tops_1])).
% 53.44/53.69  thf('46', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]:
% 53.44/53.69         (~ (l1_pre_topc @ sk_A)
% 53.44/53.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 53.44/53.69             (k1_tops_1 @ sk_A @ X1))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 53.44/53.69      inference('sup-', [status(thm)], ['44', '45'])).
% 53.44/53.69  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('48', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 53.44/53.69             (k1_tops_1 @ sk_A @ X1))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 53.44/53.69      inference('demod', [status(thm)], ['46', '47'])).
% 53.44/53.69  thf('49', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 53.44/53.69             (k1_tops_1 @ sk_A @ sk_B)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['39', '48'])).
% 53.44/53.69  thf('50', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['29', '30'])).
% 53.44/53.69  thf('51', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 53.44/53.69          (k1_tops_1 @ sk_A @ sk_B))),
% 53.44/53.69      inference('demod', [status(thm)], ['49', '50'])).
% 53.44/53.69  thf('52', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 53.44/53.69      inference('demod', [status(thm)], ['23', '24'])).
% 53.44/53.69  thf('53', plain,
% 53.44/53.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('54', plain,
% 53.44/53.69      (![X30 : $i, X31 : $i]:
% 53.44/53.69         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t3_subset])).
% 53.44/53.69  thf('55', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 53.44/53.69      inference('sup-', [status(thm)], ['53', '54'])).
% 53.44/53.69  thf('56', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 53.44/53.69      inference('demod', [status(thm)], ['23', '24'])).
% 53.44/53.69  thf('57', plain,
% 53.44/53.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X10 @ X11)
% 53.44/53.69          | ~ (r1_tarski @ X11 @ X12)
% 53.44/53.69          | (r1_tarski @ X10 @ X12))),
% 53.44/53.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 53.44/53.69  thf('58', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 53.44/53.69          | ~ (r1_tarski @ sk_C @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['56', '57'])).
% 53.44/53.69  thf('59', plain,
% 53.44/53.69      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 53.44/53.69      inference('sup-', [status(thm)], ['55', '58'])).
% 53.44/53.69  thf('60', plain,
% 53.44/53.69      (![X30 : $i, X32 : $i]:
% 53.44/53.69         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 53.44/53.69      inference('cnf', [status(esa)], [t3_subset])).
% 53.44/53.69  thf('61', plain,
% 53.44/53.69      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 53.44/53.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['59', '60'])).
% 53.44/53.69  thf('62', plain,
% 53.44/53.69      (![X33 : $i, X34 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ X34 @ X33) @ X33)
% 53.44/53.69          | ~ (l1_pre_topc @ X34))),
% 53.44/53.69      inference('cnf', [status(esa)], [t44_tops_1])).
% 53.44/53.69  thf('63', plain,
% 53.44/53.69      ((~ (l1_pre_topc @ sk_A)
% 53.44/53.69        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 53.44/53.69           (k1_tops_1 @ sk_A @ sk_C)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['61', '62'])).
% 53.44/53.69  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('65', plain,
% 53.44/53.69      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 53.44/53.69        (k1_tops_1 @ sk_A @ sk_C))),
% 53.44/53.69      inference('demod', [status(thm)], ['63', '64'])).
% 53.44/53.69  thf('66', plain,
% 53.44/53.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X10 @ X11)
% 53.44/53.69          | ~ (r1_tarski @ X11 @ X12)
% 53.44/53.69          | (r1_tarski @ X10 @ X12))),
% 53.44/53.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 53.44/53.69  thf('67', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ X0)
% 53.44/53.69          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['65', '66'])).
% 53.44/53.69  thf('68', plain,
% 53.44/53.69      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)),
% 53.44/53.69      inference('sup-', [status(thm)], ['52', '67'])).
% 53.44/53.69  thf('69', plain,
% 53.44/53.69      (![X8 : $i, X9 : $i]:
% 53.44/53.69         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 53.44/53.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 53.44/53.69  thf('70', plain,
% 53.44/53.69      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)
% 53.44/53.69         = (sk_C))),
% 53.44/53.69      inference('sup-', [status(thm)], ['68', '69'])).
% 53.44/53.69  thf('71', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 53.44/53.69      inference('sup-', [status(thm)], ['32', '33'])).
% 53.44/53.69  thf('72', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 53.44/53.69          (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 53.44/53.69      inference('sup+', [status(thm)], ['70', '71'])).
% 53.44/53.69  thf('73', plain,
% 53.44/53.69      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 53.44/53.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 53.44/53.69  thf('74', plain,
% 53.44/53.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 53.44/53.69         ((r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 53.44/53.69          | ~ (r1_xboole_0 @ X16 @ X17)
% 53.44/53.69          | ~ (r1_xboole_0 @ X16 @ X18))),
% 53.44/53.69      inference('cnf', [status(esa)], [t70_xboole_1])).
% 53.44/53.69  thf('75', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 53.44/53.69          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['73', '74'])).
% 53.44/53.69  thf('76', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 53.44/53.69          (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 53.44/53.69      inference('sup-', [status(thm)], ['72', '75'])).
% 53.44/53.69  thf('77', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 53.44/53.69          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['42', '43'])).
% 53.44/53.69  thf('78', plain,
% 53.44/53.69      (![X33 : $i, X34 : $i]:
% 53.44/53.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ X34 @ X33) @ X33)
% 53.44/53.69          | ~ (l1_pre_topc @ X34))),
% 53.44/53.69      inference('cnf', [status(esa)], [t44_tops_1])).
% 53.44/53.69  thf('79', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (~ (l1_pre_topc @ sk_A)
% 53.44/53.69          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 53.44/53.69             (k4_xboole_0 @ sk_B @ X0)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['77', '78'])).
% 53.44/53.69  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 53.44/53.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.44/53.69  thf('81', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 53.44/53.69          (k4_xboole_0 @ sk_B @ X0))),
% 53.44/53.69      inference('demod', [status(thm)], ['79', '80'])).
% 53.44/53.69  thf(t63_xboole_1, axiom,
% 53.44/53.69    (![A:$i,B:$i,C:$i]:
% 53.44/53.69     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 53.44/53.69       ( r1_xboole_0 @ A @ C ) ))).
% 53.44/53.69  thf('82', plain,
% 53.44/53.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X13 @ X14)
% 53.44/53.69          | ~ (r1_xboole_0 @ X14 @ X15)
% 53.44/53.69          | (r1_xboole_0 @ X13 @ X15))),
% 53.44/53.69      inference('cnf', [status(esa)], [t63_xboole_1])).
% 53.44/53.69  thf('83', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]:
% 53.44/53.69         ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1)
% 53.44/53.69          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 53.44/53.69      inference('sup-', [status(thm)], ['81', '82'])).
% 53.44/53.69  thf('84', plain,
% 53.44/53.69      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69        (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 53.44/53.69      inference('sup-', [status(thm)], ['76', '83'])).
% 53.44/53.69  thf('85', plain,
% 53.44/53.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X22 @ X23)
% 53.44/53.69          | ~ (r1_xboole_0 @ X22 @ X24)
% 53.44/53.69          | (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X24)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 53.44/53.69  thf('86', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69           (k4_xboole_0 @ X0 @ 
% 53.44/53.69            (k2_xboole_0 @ sk_C @ 
% 53.44/53.69             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))))
% 53.44/53.69          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69               X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['84', '85'])).
% 53.44/53.69  thf('87', plain,
% 53.44/53.69      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)
% 53.44/53.69         = (sk_C))),
% 53.44/53.69      inference('sup-', [status(thm)], ['68', '69'])).
% 53.44/53.69  thf('88', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 53.44/53.69      inference('simplify', [status(thm)], ['28'])).
% 53.44/53.69  thf('89', plain,
% 53.44/53.69      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 53.44/53.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 53.44/53.69  thf('90', plain,
% 53.44/53.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X22 @ X23)
% 53.44/53.69          | ~ (r1_xboole_0 @ X22 @ X24)
% 53.44/53.69          | (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X24)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 53.44/53.69  thf('91', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['89', '90'])).
% 53.44/53.69  thf('92', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 53.44/53.69          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['88', '91'])).
% 53.44/53.69  thf('93', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['29', '30'])).
% 53.44/53.69  thf('94', plain,
% 53.44/53.69      (![X0 : $i, X2 : $i]:
% 53.44/53.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 53.44/53.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 53.44/53.69  thf('95', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 53.44/53.69          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['93', '94'])).
% 53.44/53.69  thf('96', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ X1 @ X0)
% 53.44/53.69           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['92', '95'])).
% 53.44/53.69  thf('97', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)) @ 
% 53.44/53.69          (k4_xboole_0 @ X0 @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['31', '36'])).
% 53.44/53.69  thf('98', plain,
% 53.44/53.69      (![X0 : $i, X2 : $i]:
% 53.44/53.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 53.44/53.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 53.44/53.69  thf('99', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 53.44/53.69             (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))
% 53.44/53.69          | ((k4_xboole_0 @ X1 @ X0)
% 53.44/53.69              = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))))),
% 53.44/53.69      inference('sup-', [status(thm)], ['97', '98'])).
% 53.44/53.69  thf('100', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (~ (r1_tarski @ 
% 53.44/53.69             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 53.44/53.69             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 53.44/53.69          | ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 53.44/53.69              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 53.44/53.69                 (k2_xboole_0 @ X1 @ X0))))),
% 53.44/53.69      inference('sup-', [status(thm)], ['96', '99'])).
% 53.44/53.69  thf('101', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['29', '30'])).
% 53.44/53.69  thf('102', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ X1 @ X0)
% 53.44/53.69           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['92', '95'])).
% 53.44/53.69  thf('103', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 53.44/53.69           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 53.44/53.69      inference('demod', [status(thm)], ['100', '101', '102'])).
% 53.44/53.69  thf('104', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['29', '30'])).
% 53.44/53.69  thf('105', plain,
% 53.44/53.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k4_xboole_0 @ X5 @ X7) @ X6))),
% 53.44/53.69      inference('cnf', [status(esa)], [t109_xboole_1])).
% 53.44/53.69  thf('106', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['104', '105'])).
% 53.44/53.69  thf('107', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['89', '90'])).
% 53.44/53.69  thf('108', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 53.44/53.69          (k4_xboole_0 @ X0 @ X1))),
% 53.44/53.69      inference('sup-', [status(thm)], ['106', '107'])).
% 53.44/53.69  thf('109', plain,
% 53.44/53.69      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 53.44/53.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 53.44/53.69  thf('110', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['29', '30'])).
% 53.44/53.69  thf('111', plain,
% 53.44/53.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X13 @ X14)
% 53.44/53.69          | ~ (r1_xboole_0 @ X14 @ X15)
% 53.44/53.69          | (r1_xboole_0 @ X13 @ X15))),
% 53.44/53.69      inference('cnf', [status(esa)], [t63_xboole_1])).
% 53.44/53.69  thf('112', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 53.44/53.69          | ~ (r1_xboole_0 @ X0 @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['110', '111'])).
% 53.44/53.69  thf('113', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['109', '112'])).
% 53.44/53.69  thf('114', plain,
% 53.44/53.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X22 @ X23)
% 53.44/53.69          | ~ (r1_xboole_0 @ X22 @ X24)
% 53.44/53.69          | (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X24)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 53.44/53.69  thf('115', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.44/53.69         ((r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 53.44/53.69           (k4_xboole_0 @ X3 @ X0))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 53.44/53.69      inference('sup-', [status(thm)], ['113', '114'])).
% 53.44/53.69  thf('116', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 53.44/53.69          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['108', '115'])).
% 53.44/53.69  thf('117', plain,
% 53.44/53.69      (![X0 : $i, X2 : $i]:
% 53.44/53.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 53.44/53.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 53.44/53.69  thf('118', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 53.44/53.69             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))
% 53.44/53.69          | ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 53.44/53.69              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['116', '117'])).
% 53.44/53.69  thf('119', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 53.44/53.69          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['108', '115'])).
% 53.44/53.69  thf('120', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 53.44/53.69           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 53.44/53.69      inference('demod', [status(thm)], ['118', '119'])).
% 53.44/53.69  thf('121', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 53.44/53.69           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 53.44/53.69      inference('demod', [status(thm)], ['103', '120'])).
% 53.44/53.69  thf('122', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['104', '105'])).
% 53.44/53.69  thf('123', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['109', '112'])).
% 53.44/53.69  thf('124', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 53.44/53.69          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['73', '74'])).
% 53.44/53.69  thf('125', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 53.44/53.69          (k2_xboole_0 @ X1 @ X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['123', '124'])).
% 53.44/53.69  thf('126', plain,
% 53.44/53.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X22 @ X23)
% 53.44/53.69          | ~ (r1_xboole_0 @ X22 @ X24)
% 53.44/53.69          | (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X24)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 53.44/53.69  thf('127', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.44/53.69         ((r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 53.44/53.69           (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X1 @ X0)))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 53.44/53.69      inference('sup-', [status(thm)], ['125', '126'])).
% 53.44/53.69  thf('128', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 53.44/53.69          (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['122', '127'])).
% 53.44/53.69  thf('129', plain,
% 53.44/53.69      (![X0 : $i, X2 : $i]:
% 53.44/53.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 53.44/53.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 53.44/53.69  thf('130', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 53.44/53.69             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))
% 53.44/53.69          | ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 53.44/53.69              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['128', '129'])).
% 53.44/53.69  thf('131', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['29', '30'])).
% 53.44/53.69  thf('132', plain,
% 53.44/53.69      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 53.44/53.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 53.44/53.69  thf('133', plain,
% 53.44/53.69      (![X16 : $i, X17 : $i, X19 : $i]:
% 53.44/53.69         ((r1_xboole_0 @ X16 @ X19)
% 53.44/53.69          | ~ (r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X19)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t70_xboole_1])).
% 53.44/53.69  thf('134', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 53.44/53.69      inference('sup-', [status(thm)], ['132', '133'])).
% 53.44/53.69  thf('135', plain,
% 53.44/53.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X22 @ X23)
% 53.44/53.69          | ~ (r1_xboole_0 @ X22 @ X24)
% 53.44/53.69          | (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X24)))),
% 53.44/53.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 53.44/53.69  thf('136', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.44/53.69         ((r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 53.44/53.69           (k4_xboole_0 @ X3 @ X0))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 53.44/53.69      inference('sup-', [status(thm)], ['134', '135'])).
% 53.44/53.69  thf('137', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)) @ 
% 53.44/53.69          (k4_xboole_0 @ X0 @ X1))),
% 53.44/53.69      inference('sup-', [status(thm)], ['131', '136'])).
% 53.44/53.69  thf('138', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.44/53.69         ((r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 53.44/53.69           (k4_xboole_0 @ X3 @ X0))
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X3))),
% 53.44/53.69      inference('sup-', [status(thm)], ['34', '35'])).
% 53.44/53.69  thf('139', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         (r1_tarski @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0)) @ 
% 53.44/53.69          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 53.44/53.69      inference('sup-', [status(thm)], ['137', '138'])).
% 53.44/53.69  thf('140', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 53.44/53.69           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 53.44/53.69      inference('demod', [status(thm)], ['130', '139'])).
% 53.44/53.69  thf('141', plain,
% 53.44/53.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 53.44/53.69           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 53.44/53.69      inference('demod', [status(thm)], ['121', '140'])).
% 53.44/53.69  thf('142', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ X0 @ 
% 53.44/53.69           (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 53.44/53.69           = (k4_xboole_0 @ X0 @ 
% 53.44/53.69              (k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 53.44/53.69               sk_C)))),
% 53.44/53.69      inference('sup+', [status(thm)], ['87', '141'])).
% 53.44/53.69  thf('143', plain,
% 53.44/53.69      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)
% 53.44/53.69         = (sk_C))),
% 53.44/53.69      inference('sup-', [status(thm)], ['68', '69'])).
% 53.44/53.69  thf('144', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((k4_xboole_0 @ X0 @ 
% 53.44/53.69           (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 53.44/53.69           = (k4_xboole_0 @ X0 @ sk_C))),
% 53.44/53.69      inference('demod', [status(thm)], ['142', '143'])).
% 53.44/53.69  thf('145', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69           (k4_xboole_0 @ X0 @ sk_C))
% 53.44/53.69          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69               X0))),
% 53.44/53.69      inference('demod', [status(thm)], ['86', '144'])).
% 53.44/53.69  thf('146', plain,
% 53.44/53.69      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_C))),
% 53.44/53.69      inference('sup-', [status(thm)], ['51', '145'])).
% 53.44/53.69  thf('147', plain,
% 53.44/53.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 53.44/53.69         (~ (r1_tarski @ X10 @ X11)
% 53.44/53.69          | ~ (r1_tarski @ X11 @ X12)
% 53.44/53.69          | (r1_tarski @ X10 @ X12))),
% 53.44/53.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 53.44/53.69  thf('148', plain,
% 53.44/53.69      (![X0 : $i]:
% 53.44/53.69         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ X0)
% 53.44/53.69          | ~ (r1_tarski @ (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_C) @ 
% 53.44/53.69               X0))),
% 53.44/53.69      inference('sup-', [status(thm)], ['146', '147'])).
% 53.44/53.69  thf('149', plain,
% 53.44/53.69      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 53.44/53.69        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 53.44/53.69      inference('sup-', [status(thm)], ['38', '148'])).
% 53.44/53.69  thf('150', plain, ($false), inference('demod', [status(thm)], ['20', '149'])).
% 53.44/53.69  
% 53.44/53.69  % SZS output end Refutation
% 53.44/53.69  
% 53.51/53.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
