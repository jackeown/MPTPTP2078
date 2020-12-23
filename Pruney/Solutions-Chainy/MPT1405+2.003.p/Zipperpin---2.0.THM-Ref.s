%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FaMalKpyQc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:14 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 202 expanded)
%              Number of leaves         :   38 (  78 expanded)
%              Depth                    :   22
%              Number of atoms          :  752 (1456 expanded)
%              Number of equality atoms :   39 (  57 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('0',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X41: $i] :
      ( ( ( k1_tops_1 @ X41 @ ( k2_struct_0 @ X41 ) )
        = ( k2_struct_0 @ X41 ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('3',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X27: $i] :
      ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X34 @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc1_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X45: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( ( k3_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k3_xboole_0 @ X5 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( ( k3_xboole_0 @ X26 @ ( k1_tarski @ X25 ) )
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t51_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['37','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['16','55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('58',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( r1_tarski @ X42 @ ( k1_tops_1 @ X43 @ X44 ) )
      | ( m2_connsp_2 @ X44 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('70',plain,(
    ! [X40: $i] :
      ( ( l1_struct_0 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','72'])).

thf('74',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    r1_tarski @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['73','80','81','82'])).

thf('84',plain,
    ( ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_2 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('86',plain,(
    m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FaMalKpyQc
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.73  % Solved by: fo/fo7.sh
% 0.49/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.73  % done 592 iterations in 0.280s
% 0.49/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.73  % SZS output start Refutation
% 0.49/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.73  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.49/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.73  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.49/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.49/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.49/0.73  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.49/0.73  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.49/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.73  thf(t35_connsp_2, conjecture,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.73       ( ![B:$i]:
% 0.49/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.73           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.49/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.73    (~( ![A:$i]:
% 0.49/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.49/0.73            ( l1_pre_topc @ A ) ) =>
% 0.49/0.73          ( ![B:$i]:
% 0.49/0.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.73              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.49/0.73    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.49/0.73  thf('0', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_2)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(d3_struct_0, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.49/0.73  thf('1', plain,
% 0.49/0.73      (![X39 : $i]:
% 0.49/0.73         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.49/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.73  thf(t43_tops_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.73       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.49/0.73  thf('2', plain,
% 0.49/0.73      (![X41 : $i]:
% 0.49/0.73         (((k1_tops_1 @ X41 @ (k2_struct_0 @ X41)) = (k2_struct_0 @ X41))
% 0.49/0.73          | ~ (l1_pre_topc @ X41)
% 0.49/0.73          | ~ (v2_pre_topc @ X41))),
% 0.49/0.73      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.49/0.73  thf('3', plain,
% 0.49/0.73      (![X39 : $i]:
% 0.49/0.73         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.49/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.73  thf(t80_zfmisc_1, axiom,
% 0.49/0.73    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.73  thf('4', plain,
% 0.49/0.73      (![X27 : $i]: (r1_tarski @ (k1_tarski @ X27) @ (k1_zfmisc_1 @ X27))),
% 0.49/0.73      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.49/0.73  thf(t28_xboole_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.49/0.73  thf('5', plain,
% 0.49/0.73      (![X14 : $i, X15 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.49/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.73  thf('6', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))
% 0.49/0.73           = (k1_tarski @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.73  thf(l27_zfmisc_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.49/0.73  thf('7', plain,
% 0.49/0.73      (![X20 : $i, X21 : $i]:
% 0.49/0.73         ((r1_xboole_0 @ (k1_tarski @ X20) @ X21) | (r2_hidden @ X20 @ X21))),
% 0.49/0.73      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.49/0.73  thf(d7_xboole_0, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.49/0.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.73  thf('8', plain,
% 0.49/0.73      (![X5 : $i, X6 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.49/0.73  thf('9', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         ((r2_hidden @ X1 @ X0)
% 0.49/0.73          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.73  thf('10', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.73          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.49/0.73      inference('sup+', [status(thm)], ['6', '9'])).
% 0.49/0.73  thf(t1_subset, axiom,
% 0.49/0.73    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.49/0.73  thf('11', plain,
% 0.49/0.73      (![X34 : $i, X35 : $i]:
% 0.49/0.73         ((m1_subset_1 @ X34 @ X35) | ~ (r2_hidden @ X34 @ X35))),
% 0.49/0.73      inference('cnf', [status(esa)], [t1_subset])).
% 0.49/0.73  thf('12', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.49/0.73          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.73  thf(t3_subset, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.73  thf('13', plain,
% 0.49/0.73      (![X36 : $i, X37 : $i]:
% 0.49/0.73         ((r1_tarski @ X36 @ X37) | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.73  thf('14', plain,
% 0.49/0.73      (![X0 : $i]: (((k1_tarski @ X0) = (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.73  thf('15', plain,
% 0.49/0.73      (![X14 : $i, X15 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.49/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.73  thf('16', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_tarski @ X0) = (k1_xboole_0)) | ((k3_xboole_0 @ X0 @ X0) = (X0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.49/0.73  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(rc1_connsp_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( l1_pre_topc @ A ) =>
% 0.49/0.73       ( ?[B:$i]:
% 0.49/0.73         ( ( v1_xboole_0 @ B ) & 
% 0.49/0.73           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.49/0.73  thf('18', plain,
% 0.49/0.73      (![X45 : $i]: ((v1_xboole_0 @ (sk_B_1 @ X45)) | ~ (l1_pre_topc @ X45))),
% 0.49/0.73      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.49/0.73  thf(t3_xboole_0, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.49/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.73            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.49/0.73  thf('19', plain,
% 0.49/0.73      (![X8 : $i, X9 : $i]:
% 0.49/0.73         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.73  thf(d1_xboole_0, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.73  thf('20', plain,
% 0.49/0.73      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.49/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.73  thf('21', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.73  thf('22', plain,
% 0.49/0.73      (![X5 : $i, X6 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.49/0.73  thf('23', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.73  thf('24', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.73  thf(t17_xboole_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.73  thf('25', plain,
% 0.49/0.73      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.49/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.49/0.73  thf('26', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.49/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.49/0.73  thf('27', plain,
% 0.49/0.73      (![X36 : $i, X38 : $i]:
% 0.49/0.73         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.73  thf('28', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.73  thf('29', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | ~ (v1_xboole_0 @ X1))),
% 0.49/0.73      inference('sup+', [status(thm)], ['23', '28'])).
% 0.49/0.73  thf('30', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (~ (l1_pre_topc @ X0)
% 0.49/0.73          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['18', '29'])).
% 0.49/0.73  thf('31', plain,
% 0.49/0.73      (![X36 : $i, X37 : $i]:
% 0.49/0.73         ((r1_tarski @ X36 @ X37) | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.73  thf('32', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (~ (l1_pre_topc @ X1) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.73  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.49/0.73      inference('sup-', [status(thm)], ['17', '32'])).
% 0.49/0.73  thf('34', plain,
% 0.49/0.73      (![X14 : $i, X15 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.49/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.73  thf('35', plain,
% 0.49/0.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.73  thf(t51_zfmisc_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.49/0.73       ( r2_hidden @ B @ A ) ))).
% 0.49/0.73  thf('36', plain,
% 0.49/0.73      (![X25 : $i, X26 : $i]:
% 0.49/0.73         ((r2_hidden @ X25 @ X26)
% 0.49/0.73          | ((k3_xboole_0 @ X26 @ (k1_tarski @ X25)) != (k1_tarski @ X25)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t51_zfmisc_1])).
% 0.49/0.73  thf('37', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.73  thf('38', plain,
% 0.49/0.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.73  thf('39', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.73  thf('40', plain,
% 0.49/0.73      (![X5 : $i, X7 : $i]:
% 0.49/0.73         ((r1_xboole_0 @ X5 @ X7) | ((k3_xboole_0 @ X5 @ X7) != (k1_xboole_0)))),
% 0.49/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.49/0.73  thf('41', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.73  thf('42', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['38', '41'])).
% 0.49/0.73  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.49/0.73      inference('simplify', [status(thm)], ['42'])).
% 0.49/0.73  thf('44', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))
% 0.49/0.73           = (k1_tarski @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.73  thf('45', plain,
% 0.49/0.73      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.49/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.49/0.73  thf('46', plain,
% 0.49/0.73      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['44', '45'])).
% 0.49/0.73  thf('47', plain,
% 0.49/0.73      (![X14 : $i, X15 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.49/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.73  thf('48', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.49/0.73           = (k1_tarski @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.49/0.73  thf('49', plain,
% 0.49/0.73      (![X25 : $i, X26 : $i]:
% 0.49/0.73         ((r2_hidden @ X25 @ X26)
% 0.49/0.73          | ((k3_xboole_0 @ X26 @ (k1_tarski @ X25)) != (k1_tarski @ X25)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t51_zfmisc_1])).
% 0.49/0.73  thf('50', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.49/0.73          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.73  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['50'])).
% 0.49/0.73  thf('52', plain,
% 0.49/0.73      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.49/0.73         (~ (r2_hidden @ X10 @ X8)
% 0.49/0.73          | ~ (r2_hidden @ X10 @ X11)
% 0.49/0.73          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.49/0.73  thf('53', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['51', '52'])).
% 0.49/0.73  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.49/0.73      inference('sup-', [status(thm)], ['43', '53'])).
% 0.49/0.73  thf('55', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.49/0.73      inference('clc', [status(thm)], ['37', '54'])).
% 0.49/0.73  thf('56', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.73      inference('clc', [status(thm)], ['16', '55'])).
% 0.49/0.73  thf('57', plain,
% 0.49/0.73      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.49/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.49/0.73  thf('58', plain,
% 0.49/0.73      (![X36 : $i, X38 : $i]:
% 0.49/0.73         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.73  thf('59', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.73  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.73      inference('sup+', [status(thm)], ['56', '59'])).
% 0.49/0.73  thf('61', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(d2_connsp_2, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.73       ( ![B:$i]:
% 0.49/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.73           ( ![C:$i]:
% 0.49/0.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.73               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.49/0.73                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.49/0.73  thf('62', plain,
% 0.49/0.73      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.49/0.73          | ~ (r1_tarski @ X42 @ (k1_tops_1 @ X43 @ X44))
% 0.49/0.73          | (m2_connsp_2 @ X44 @ X43 @ X42)
% 0.49/0.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.49/0.73          | ~ (l1_pre_topc @ X43)
% 0.49/0.73          | ~ (v2_pre_topc @ X43))),
% 0.49/0.73      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.49/0.73  thf('63', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (v2_pre_topc @ sk_A)
% 0.49/0.73          | ~ (l1_pre_topc @ sk_A)
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.73          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_2)
% 0.49/0.73          | ~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['61', '62'])).
% 0.49/0.73  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('66', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.73          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_2)
% 0.49/0.73          | ~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.49/0.73      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.49/0.73  thf('67', plain,
% 0.49/0.73      ((~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.49/0.73        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.49/0.73      inference('sup-', [status(thm)], ['60', '66'])).
% 0.49/0.73  thf('68', plain,
% 0.49/0.73      ((~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.49/0.73        | ~ (l1_struct_0 @ sk_A)
% 0.49/0.73        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.49/0.73      inference('sup-', [status(thm)], ['3', '67'])).
% 0.49/0.73  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(dt_l1_pre_topc, axiom,
% 0.49/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.49/0.73  thf('70', plain,
% 0.49/0.73      (![X40 : $i]: ((l1_struct_0 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.49/0.73  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.73      inference('sup-', [status(thm)], ['69', '70'])).
% 0.49/0.73  thf('72', plain,
% 0.49/0.73      ((~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.49/0.73        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.49/0.73      inference('demod', [status(thm)], ['68', '71'])).
% 0.49/0.73  thf('73', plain,
% 0.49/0.73      ((~ (r1_tarski @ sk_B_2 @ (k2_struct_0 @ sk_A))
% 0.49/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.73        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.49/0.73      inference('sup-', [status(thm)], ['2', '72'])).
% 0.49/0.73  thf('74', plain,
% 0.49/0.73      (![X39 : $i]:
% 0.49/0.73         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.49/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.73  thf('75', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('76', plain,
% 0.49/0.73      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.49/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.73      inference('sup+', [status(thm)], ['74', '75'])).
% 0.49/0.73  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.73      inference('sup-', [status(thm)], ['69', '70'])).
% 0.49/0.73  thf('78', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.49/0.73      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.73  thf('79', plain,
% 0.49/0.73      (![X36 : $i, X37 : $i]:
% 0.49/0.73         ((r1_tarski @ X36 @ X37) | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.49/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.73  thf('80', plain, ((r1_tarski @ sk_B_2 @ (k2_struct_0 @ sk_A))),
% 0.49/0.73      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.73  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('83', plain, ((m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2)),
% 0.49/0.73      inference('demod', [status(thm)], ['73', '80', '81', '82'])).
% 0.49/0.73  thf('84', plain,
% 0.49/0.73      (((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_2)
% 0.49/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.73      inference('sup+', [status(thm)], ['1', '83'])).
% 0.49/0.73  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.73      inference('sup-', [status(thm)], ['69', '70'])).
% 0.49/0.73  thf('86', plain, ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_2)),
% 0.49/0.73      inference('demod', [status(thm)], ['84', '85'])).
% 0.49/0.73  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 0.49/0.73  
% 0.49/0.73  % SZS output end Refutation
% 0.49/0.73  
% 0.49/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
