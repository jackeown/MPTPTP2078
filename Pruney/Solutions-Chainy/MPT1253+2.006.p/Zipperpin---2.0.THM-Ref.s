%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DnI8HzK5po

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:13 EST 2020

% Result     : Theorem 4.55s
% Output     : Refutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 362 expanded)
%              Number of leaves         :   45 ( 133 expanded)
%              Depth                    :   22
%              Number of atoms          : 1012 (2817 expanded)
%              Number of equality atoms :   65 ( 189 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ ( k6_subset_1 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( k6_subset_1 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X21: $i] :
      ( ( k6_subset_1 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) )
      = ( k3_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) )
      = ( k3_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ ( k6_subset_1 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('43',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('45',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('46',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( l1_pre_topc @ X61 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X61 @ X62 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X43: $i,X44: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X49 ) )
      | ( ( k4_subset_1 @ X49 @ X48 @ X50 )
        = ( k2_xboole_0 @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ( ( k2_pre_topc @ X69 @ X68 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X69 ) @ X68 @ ( k2_tops_1 @ X69 @ X68 ) ) )
      | ~ ( l1_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('63',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','61','62'])).

thf('64',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('70',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( v4_pre_topc @ X63 @ X64 )
      | ~ ( r1_tarski @ X65 @ X63 )
      | ( r1_tarski @ ( k2_pre_topc @ X64 @ X65 ) @ X63 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('80',plain,
    ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','86'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('88',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('89',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('90',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X17 @ X18 ) @ X17 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('91',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('92',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k6_subset_1 @ X51 @ X52 )
      = ( k4_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('93',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X25 @ X26 ) @ X27 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['87','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DnI8HzK5po
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:59:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.55/4.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.55/4.79  % Solved by: fo/fo7.sh
% 4.55/4.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.55/4.79  % done 10508 iterations in 4.330s
% 4.55/4.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.55/4.79  % SZS output start Refutation
% 4.55/4.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.55/4.79  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 4.55/4.79  thf(sk_B_type, type, sk_B: $i).
% 4.55/4.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.55/4.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.55/4.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.55/4.79  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.55/4.79  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 4.55/4.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.55/4.79  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.55/4.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.55/4.79  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.55/4.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.55/4.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.55/4.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.55/4.79  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 4.55/4.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.55/4.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.55/4.79  thf(sk_A_type, type, sk_A: $i).
% 4.55/4.79  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.55/4.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.55/4.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.55/4.79  thf(t69_tops_1, conjecture,
% 4.55/4.79    (![A:$i]:
% 4.55/4.79     ( ( l1_pre_topc @ A ) =>
% 4.55/4.79       ( ![B:$i]:
% 4.55/4.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.55/4.79           ( ( v4_pre_topc @ B @ A ) =>
% 4.55/4.79             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 4.55/4.79  thf(zf_stmt_0, negated_conjecture,
% 4.55/4.79    (~( ![A:$i]:
% 4.55/4.79        ( ( l1_pre_topc @ A ) =>
% 4.55/4.79          ( ![B:$i]:
% 4.55/4.79            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.55/4.79              ( ( v4_pre_topc @ B @ A ) =>
% 4.55/4.79                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 4.55/4.79    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 4.55/4.79  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(t7_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.55/4.79  thf('1', plain,
% 4.55/4.79      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 4.55/4.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.55/4.79  thf(d3_tarski, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( r1_tarski @ A @ B ) <=>
% 4.55/4.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.55/4.79  thf('2', plain,
% 4.55/4.79      (![X1 : $i, X3 : $i]:
% 4.55/4.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_tarski])).
% 4.55/4.79  thf('3', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(l3_subset_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.55/4.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 4.55/4.79  thf('4', plain,
% 4.55/4.79      (![X45 : $i, X46 : $i, X47 : $i]:
% 4.55/4.79         (~ (r2_hidden @ X45 @ X46)
% 4.55/4.79          | (r2_hidden @ X45 @ X47)
% 4.55/4.79          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 4.55/4.79      inference('cnf', [status(esa)], [l3_subset_1])).
% 4.55/4.79  thf('5', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 4.55/4.79      inference('sup-', [status(thm)], ['3', '4'])).
% 4.55/4.79  thf('6', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((r1_tarski @ sk_B @ X0)
% 4.55/4.79          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['2', '5'])).
% 4.55/4.79  thf('7', plain,
% 4.55/4.79      (![X1 : $i, X3 : $i]:
% 4.55/4.79         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_tarski])).
% 4.55/4.79  thf('8', plain,
% 4.55/4.79      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 4.55/4.79        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['6', '7'])).
% 4.55/4.79  thf('9', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.55/4.79      inference('simplify', [status(thm)], ['8'])).
% 4.55/4.79  thf(t12_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.55/4.79  thf('10', plain,
% 4.55/4.79      (![X12 : $i, X13 : $i]:
% 4.55/4.79         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 4.55/4.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.55/4.79  thf('11', plain,
% 4.55/4.79      (((k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 4.55/4.79      inference('sup-', [status(thm)], ['9', '10'])).
% 4.55/4.79  thf(t11_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 4.55/4.79  thf('12', plain,
% 4.55/4.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.55/4.79         ((r1_tarski @ X9 @ X10)
% 4.55/4.79          | ~ (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 4.55/4.79      inference('cnf', [status(esa)], [t11_xboole_1])).
% 4.55/4.79  thf('13', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         (~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0) | (r1_tarski @ sk_B @ X0))),
% 4.55/4.79      inference('sup-', [status(thm)], ['11', '12'])).
% 4.55/4.79  thf('14', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 4.55/4.79      inference('sup-', [status(thm)], ['1', '13'])).
% 4.55/4.79  thf(t43_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 4.55/4.79       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 4.55/4.79  thf('15', plain,
% 4.55/4.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.55/4.79         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 4.55/4.79          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 4.55/4.79      inference('cnf', [status(esa)], [t43_xboole_1])).
% 4.55/4.79  thf(redefinition_k6_subset_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.55/4.79  thf('16', plain,
% 4.55/4.79      (![X51 : $i, X52 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.79  thf('17', plain,
% 4.55/4.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.55/4.79         ((r1_tarski @ (k6_subset_1 @ X22 @ X23) @ X24)
% 4.55/4.79          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 4.55/4.79      inference('demod', [status(thm)], ['15', '16'])).
% 4.55/4.79  thf('18', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         (r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 4.55/4.79      inference('sup-', [status(thm)], ['14', '17'])).
% 4.55/4.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.55/4.79  thf('19', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 4.55/4.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.55/4.79  thf(d10_xboole_0, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.55/4.79  thf('20', plain,
% 4.55/4.79      (![X4 : $i, X6 : $i]:
% 4.55/4.79         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.55/4.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.55/4.79  thf('21', plain,
% 4.55/4.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['19', '20'])).
% 4.55/4.79  thf('22', plain,
% 4.55/4.79      (((k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 4.55/4.79      inference('sup-', [status(thm)], ['18', '21'])).
% 4.55/4.79  thf(t48_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.55/4.79  thf('23', plain,
% 4.55/4.79      (![X28 : $i, X29 : $i]:
% 4.55/4.79         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 4.55/4.79           = (k3_xboole_0 @ X28 @ X29))),
% 4.55/4.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.55/4.79  thf('24', plain,
% 4.55/4.79      (![X51 : $i, X52 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.79  thf('25', plain,
% 4.55/4.79      (![X51 : $i, X52 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.79  thf('26', plain,
% 4.55/4.79      (![X28 : $i, X29 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X28 @ (k6_subset_1 @ X28 @ X29))
% 4.55/4.79           = (k3_xboole_0 @ X28 @ X29))),
% 4.55/4.79      inference('demod', [status(thm)], ['23', '24', '25'])).
% 4.55/4.79  thf('27', plain,
% 4.55/4.79      (((k6_subset_1 @ sk_B @ k1_xboole_0)
% 4.55/4.79         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('sup+', [status(thm)], ['22', '26'])).
% 4.55/4.79  thf(t3_boole, axiom,
% 4.55/4.79    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.55/4.79  thf('28', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 4.55/4.79      inference('cnf', [status(esa)], [t3_boole])).
% 4.55/4.79  thf('29', plain,
% 4.55/4.79      (![X51 : $i, X52 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.79  thf('30', plain, (![X21 : $i]: ((k6_subset_1 @ X21 @ k1_xboole_0) = (X21))),
% 4.55/4.79      inference('demod', [status(thm)], ['28', '29'])).
% 4.55/4.79  thf('31', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('demod', [status(thm)], ['27', '30'])).
% 4.55/4.79  thf(commutativity_k2_tarski, axiom,
% 4.55/4.79    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.55/4.79  thf('32', plain,
% 4.55/4.79      (![X32 : $i, X33 : $i]:
% 4.55/4.79         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 4.55/4.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.55/4.79  thf(t12_setfam_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.55/4.79  thf('33', plain,
% 4.55/4.79      (![X59 : $i, X60 : $i]:
% 4.55/4.79         ((k1_setfam_1 @ (k2_tarski @ X59 @ X60)) = (k3_xboole_0 @ X59 @ X60))),
% 4.55/4.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.55/4.79  thf('34', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]:
% 4.55/4.79         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('35', plain,
% 4.55/4.79      (![X59 : $i, X60 : $i]:
% 4.55/4.79         ((k1_setfam_1 @ (k2_tarski @ X59 @ X60)) = (k3_xboole_0 @ X59 @ X60))),
% 4.55/4.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.55/4.79  thf('36', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.55/4.79      inference('sup+', [status(thm)], ['34', '35'])).
% 4.55/4.79  thf(t100_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.55/4.79  thf('37', plain,
% 4.55/4.79      (![X7 : $i, X8 : $i]:
% 4.55/4.79         ((k4_xboole_0 @ X7 @ X8)
% 4.55/4.79           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 4.55/4.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.55/4.79  thf('38', plain,
% 4.55/4.79      (![X51 : $i, X52 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.79  thf('39', plain,
% 4.55/4.79      (![X7 : $i, X8 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X7 @ X8)
% 4.55/4.79           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 4.55/4.79      inference('demod', [status(thm)], ['37', '38'])).
% 4.55/4.79  thf('40', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X0 @ X1)
% 4.55/4.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.55/4.79      inference('sup+', [status(thm)], ['36', '39'])).
% 4.55/4.79  thf('41', plain,
% 4.55/4.79      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 4.55/4.79         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['31', '40'])).
% 4.55/4.79  thf('42', plain,
% 4.55/4.79      (![X28 : $i, X29 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X28 @ (k6_subset_1 @ X28 @ X29))
% 4.55/4.79           = (k3_xboole_0 @ X28 @ X29))),
% 4.55/4.79      inference('demod', [status(thm)], ['23', '24', '25'])).
% 4.55/4.79  thf('43', plain,
% 4.55/4.79      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.79         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 4.55/4.79         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['41', '42'])).
% 4.55/4.79  thf('44', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.55/4.79      inference('sup+', [status(thm)], ['34', '35'])).
% 4.55/4.79  thf('45', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('demod', [status(thm)], ['27', '30'])).
% 4.55/4.79  thf('46', plain,
% 4.55/4.79      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.79         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['43', '44', '45'])).
% 4.55/4.79  thf('47', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(dt_k2_tops_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( ( l1_pre_topc @ A ) & 
% 4.55/4.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.55/4.79       ( m1_subset_1 @
% 4.55/4.79         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.55/4.79  thf('48', plain,
% 4.55/4.79      (![X61 : $i, X62 : $i]:
% 4.55/4.79         (~ (l1_pre_topc @ X61)
% 4.55/4.79          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 4.55/4.79          | (m1_subset_1 @ (k2_tops_1 @ X61 @ X62) @ 
% 4.55/4.79             (k1_zfmisc_1 @ (u1_struct_0 @ X61))))),
% 4.55/4.79      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 4.55/4.79  thf('49', plain,
% 4.55/4.79      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 4.55/4.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.55/4.79        | ~ (l1_pre_topc @ sk_A))),
% 4.55/4.79      inference('sup-', [status(thm)], ['47', '48'])).
% 4.55/4.79  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('51', plain,
% 4.55/4.79      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 4.55/4.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('demod', [status(thm)], ['49', '50'])).
% 4.55/4.79  thf(dt_k6_subset_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.55/4.79  thf('52', plain,
% 4.55/4.79      (![X43 : $i, X44 : $i]:
% 4.55/4.79         (m1_subset_1 @ (k6_subset_1 @ X43 @ X44) @ (k1_zfmisc_1 @ X43))),
% 4.55/4.79      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 4.55/4.79  thf(redefinition_k4_subset_1, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.55/4.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.55/4.79       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 4.55/4.79  thf('53', plain,
% 4.55/4.79      (![X48 : $i, X49 : $i, X50 : $i]:
% 4.55/4.79         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 4.55/4.79          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X49))
% 4.55/4.79          | ((k4_subset_1 @ X49 @ X48 @ X50) = (k2_xboole_0 @ X48 @ X50)))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 4.55/4.79  thf('54', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.55/4.79         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 4.55/4.79            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 4.55/4.79          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['52', '53'])).
% 4.55/4.79  thf('55', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.79           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 4.55/4.79           (k2_tops_1 @ sk_A @ sk_B))
% 4.55/4.79           = (k2_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 4.55/4.79              (k2_tops_1 @ sk_A @ sk_B)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['51', '54'])).
% 4.55/4.79  thf('56', plain,
% 4.55/4.79      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 4.55/4.79         = (k2_xboole_0 @ 
% 4.55/4.79            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.79             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 4.55/4.79            (k2_tops_1 @ sk_A @ sk_B)))),
% 4.55/4.79      inference('sup+', [status(thm)], ['46', '55'])).
% 4.55/4.79  thf('57', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(t65_tops_1, axiom,
% 4.55/4.79    (![A:$i]:
% 4.55/4.79     ( ( l1_pre_topc @ A ) =>
% 4.55/4.79       ( ![B:$i]:
% 4.55/4.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.55/4.79           ( ( k2_pre_topc @ A @ B ) =
% 4.55/4.79             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.55/4.79  thf('58', plain,
% 4.55/4.79      (![X68 : $i, X69 : $i]:
% 4.55/4.79         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 4.55/4.79          | ((k2_pre_topc @ X69 @ X68)
% 4.55/4.79              = (k4_subset_1 @ (u1_struct_0 @ X69) @ X68 @ 
% 4.55/4.79                 (k2_tops_1 @ X69 @ X68)))
% 4.55/4.79          | ~ (l1_pre_topc @ X69))),
% 4.55/4.79      inference('cnf', [status(esa)], [t65_tops_1])).
% 4.55/4.79  thf('59', plain,
% 4.55/4.79      ((~ (l1_pre_topc @ sk_A)
% 4.55/4.79        | ((k2_pre_topc @ sk_A @ sk_B)
% 4.55/4.79            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 4.55/4.79               (k2_tops_1 @ sk_A @ sk_B))))),
% 4.55/4.79      inference('sup-', [status(thm)], ['57', '58'])).
% 4.55/4.79  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('61', plain,
% 4.55/4.79      (((k2_pre_topc @ sk_A @ sk_B)
% 4.55/4.79         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 4.55/4.79            (k2_tops_1 @ sk_A @ sk_B)))),
% 4.55/4.79      inference('demod', [status(thm)], ['59', '60'])).
% 4.55/4.79  thf('62', plain,
% 4.55/4.79      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.79         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['43', '44', '45'])).
% 4.55/4.79  thf('63', plain,
% 4.55/4.79      (((k2_pre_topc @ sk_A @ sk_B)
% 4.55/4.79         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.55/4.79      inference('demod', [status(thm)], ['56', '61', '62'])).
% 4.55/4.79  thf('64', plain,
% 4.55/4.79      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 4.55/4.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.55/4.79  thf('65', plain,
% 4.55/4.79      (![X12 : $i, X13 : $i]:
% 4.55/4.79         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 4.55/4.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.55/4.79  thf('66', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]:
% 4.55/4.79         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 4.55/4.79           = (k2_xboole_0 @ X1 @ X0))),
% 4.55/4.79      inference('sup-', [status(thm)], ['64', '65'])).
% 4.55/4.79  thf('67', plain,
% 4.55/4.79      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 4.55/4.79         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.55/4.79      inference('sup+', [status(thm)], ['63', '66'])).
% 4.55/4.79  thf('68', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('69', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(t31_tops_1, axiom,
% 4.55/4.79    (![A:$i]:
% 4.55/4.79     ( ( l1_pre_topc @ A ) =>
% 4.55/4.79       ( ![B:$i]:
% 4.55/4.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.55/4.79           ( ![C:$i]:
% 4.55/4.79             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.55/4.79               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 4.55/4.79                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 4.55/4.79  thf('70', plain,
% 4.55/4.79      (![X63 : $i, X64 : $i, X65 : $i]:
% 4.55/4.79         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 4.55/4.79          | ~ (v4_pre_topc @ X63 @ X64)
% 4.55/4.79          | ~ (r1_tarski @ X65 @ X63)
% 4.55/4.79          | (r1_tarski @ (k2_pre_topc @ X64 @ X65) @ X63)
% 4.55/4.79          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 4.55/4.79          | ~ (l1_pre_topc @ X64))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_tops_1])).
% 4.55/4.79  thf('71', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         (~ (l1_pre_topc @ sk_A)
% 4.55/4.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.55/4.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 4.55/4.79          | ~ (r1_tarski @ X0 @ sk_B)
% 4.55/4.79          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 4.55/4.79      inference('sup-', [status(thm)], ['69', '70'])).
% 4.55/4.79  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('73', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('74', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.55/4.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 4.55/4.79          | ~ (r1_tarski @ X0 @ sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['71', '72', '73'])).
% 4.55/4.79  thf('75', plain,
% 4.55/4.79      ((~ (r1_tarski @ sk_B @ sk_B)
% 4.55/4.79        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.55/4.79      inference('sup-', [status(thm)], ['68', '74'])).
% 4.55/4.79  thf('76', plain,
% 4.55/4.79      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.55/4.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.55/4.79  thf('77', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.55/4.79      inference('simplify', [status(thm)], ['76'])).
% 4.55/4.79  thf('78', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 4.55/4.79      inference('demod', [status(thm)], ['75', '77'])).
% 4.55/4.79  thf('79', plain,
% 4.55/4.79      (![X12 : $i, X13 : $i]:
% 4.55/4.79         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 4.55/4.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.55/4.79  thf('80', plain,
% 4.55/4.79      (((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 4.55/4.79      inference('sup-', [status(thm)], ['78', '79'])).
% 4.55/4.79  thf('81', plain,
% 4.55/4.79      (![X32 : $i, X33 : $i]:
% 4.55/4.79         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 4.55/4.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.55/4.79  thf(l51_zfmisc_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]:
% 4.55/4.79     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.55/4.79  thf('82', plain,
% 4.55/4.79      (![X34 : $i, X35 : $i]:
% 4.55/4.79         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 4.55/4.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.55/4.79  thf('83', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]:
% 4.55/4.79         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.55/4.79      inference('sup+', [status(thm)], ['81', '82'])).
% 4.55/4.79  thf('84', plain,
% 4.55/4.79      (![X34 : $i, X35 : $i]:
% 4.55/4.79         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 4.55/4.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.55/4.79  thf('85', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.55/4.79      inference('sup+', [status(thm)], ['83', '84'])).
% 4.55/4.79  thf('86', plain,
% 4.55/4.79      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['80', '85'])).
% 4.55/4.79  thf('87', plain,
% 4.55/4.79      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.55/4.79      inference('demod', [status(thm)], ['67', '86'])).
% 4.55/4.79  thf(t36_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.55/4.79  thf('88', plain,
% 4.55/4.79      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 4.55/4.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.55/4.79  thf('89', plain,
% 4.55/4.79      (![X51 : $i, X52 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.79  thf('90', plain,
% 4.55/4.79      (![X17 : $i, X18 : $i]: (r1_tarski @ (k6_subset_1 @ X17 @ X18) @ X17)),
% 4.55/4.79      inference('demod', [status(thm)], ['88', '89'])).
% 4.55/4.79  thf(t44_xboole_1, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 4.55/4.79       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.55/4.79  thf('91', plain,
% 4.55/4.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.55/4.79         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 4.55/4.79          | ~ (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [t44_xboole_1])).
% 4.55/4.79  thf('92', plain,
% 4.55/4.79      (![X51 : $i, X52 : $i]:
% 4.55/4.79         ((k6_subset_1 @ X51 @ X52) = (k4_xboole_0 @ X51 @ X52))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.55/4.79  thf('93', plain,
% 4.55/4.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.55/4.79         ((r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 4.55/4.79          | ~ (r1_tarski @ (k6_subset_1 @ X25 @ X26) @ X27))),
% 4.55/4.79      inference('demod', [status(thm)], ['91', '92'])).
% 4.55/4.79  thf('94', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.55/4.79      inference('sup-', [status(thm)], ['90', '93'])).
% 4.55/4.79  thf('95', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.55/4.79      inference('sup+', [status(thm)], ['87', '94'])).
% 4.55/4.79  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 4.55/4.79  
% 4.55/4.79  % SZS output end Refutation
% 4.55/4.79  
% 4.55/4.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
