%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z4mzj04Awb

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:17 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 341 expanded)
%              Number of leaves         :   21 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  833 (4675 expanded)
%              Number of equality atoms :    6 (  32 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t20_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( v1_tops_2 @ B @ A )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( v1_tops_2 @ B @ A )
                    & ( v1_tops_2 @ C @ A ) )
                 => ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tops_2])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tops_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_tops_2 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_2 )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ~ ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_tops_2 @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( v1_tops_2 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_tops_2 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_C_2 )
    | ( v3_pre_topc @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ X16 @ X17 ) @ X17 )
      | ( v1_tops_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('48',plain,(
    ~ ( v3_pre_topc @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ X16 )
      | ( v1_tops_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_tops_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('56',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','33'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_tops_2 @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    ~ ( v3_pre_topc @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('68',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_A ) @ sk_C_2 ),
    inference(clc,[status(thm)],['58','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['49','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z4mzj04Awb
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.86/4.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.86/4.08  % Solved by: fo/fo7.sh
% 3.86/4.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.86/4.08  % done 3173 iterations in 3.636s
% 3.86/4.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.86/4.08  % SZS output start Refutation
% 3.86/4.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.86/4.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.86/4.08  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.86/4.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.86/4.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.86/4.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.86/4.08  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.86/4.08  thf(sk_A_type, type, sk_A: $i).
% 3.86/4.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.86/4.08  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.86/4.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.86/4.08  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 3.86/4.08  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.86/4.08  thf(sk_B_type, type, sk_B: $i).
% 3.86/4.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.86/4.08  thf(d3_tarski, axiom,
% 3.86/4.08    (![A:$i,B:$i]:
% 3.86/4.08     ( ( r1_tarski @ A @ B ) <=>
% 3.86/4.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.86/4.08  thf('0', plain,
% 3.86/4.08      (![X1 : $i, X3 : $i]:
% 3.86/4.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.86/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.86/4.08  thf(d3_xboole_0, axiom,
% 3.86/4.08    (![A:$i,B:$i,C:$i]:
% 3.86/4.08     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 3.86/4.08       ( ![D:$i]:
% 3.86/4.08         ( ( r2_hidden @ D @ C ) <=>
% 3.86/4.08           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.86/4.08  thf('1', plain,
% 3.86/4.08      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.86/4.08         (~ (r2_hidden @ X8 @ X6)
% 3.86/4.08          | (r2_hidden @ X8 @ X7)
% 3.86/4.08          | (r2_hidden @ X8 @ X5)
% 3.86/4.08          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 3.86/4.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.86/4.08  thf('2', plain,
% 3.86/4.08      (![X5 : $i, X7 : $i, X8 : $i]:
% 3.86/4.08         ((r2_hidden @ X8 @ X5)
% 3.86/4.08          | (r2_hidden @ X8 @ X7)
% 3.86/4.08          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 3.86/4.08      inference('simplify', [status(thm)], ['1'])).
% 3.86/4.08  thf('3', plain,
% 3.86/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.08         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.86/4.08          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 3.86/4.08          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 3.86/4.08      inference('sup-', [status(thm)], ['0', '2'])).
% 3.86/4.08  thf(t20_tops_2, conjecture,
% 3.86/4.08    (![A:$i]:
% 3.86/4.08     ( ( l1_pre_topc @ A ) =>
% 3.86/4.08       ( ![B:$i]:
% 3.86/4.08         ( ( m1_subset_1 @
% 3.86/4.08             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.86/4.08           ( ![C:$i]:
% 3.86/4.08             ( ( m1_subset_1 @
% 3.86/4.08                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.86/4.08               ( ( ( v1_tops_2 @ B @ A ) & ( v1_tops_2 @ C @ A ) ) =>
% 3.86/4.08                 ( v1_tops_2 @
% 3.86/4.08                   ( k4_subset_1 @
% 3.86/4.08                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 3.86/4.08                   A ) ) ) ) ) ) ))).
% 3.86/4.08  thf(zf_stmt_0, negated_conjecture,
% 3.86/4.08    (~( ![A:$i]:
% 3.86/4.08        ( ( l1_pre_topc @ A ) =>
% 3.86/4.08          ( ![B:$i]:
% 3.86/4.08            ( ( m1_subset_1 @
% 3.86/4.08                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.86/4.08              ( ![C:$i]:
% 3.86/4.08                ( ( m1_subset_1 @
% 3.86/4.08                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.86/4.08                  ( ( ( v1_tops_2 @ B @ A ) & ( v1_tops_2 @ C @ A ) ) =>
% 3.86/4.08                    ( v1_tops_2 @
% 3.86/4.08                      ( k4_subset_1 @
% 3.86/4.08                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 3.86/4.08                      A ) ) ) ) ) ) ) )),
% 3.86/4.08    inference('cnf.neg', [status(esa)], [t20_tops_2])).
% 3.86/4.08  thf('4', plain,
% 3.86/4.08      ((m1_subset_1 @ sk_B @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf(t3_subset, axiom,
% 3.86/4.08    (![A:$i,B:$i]:
% 3.86/4.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.86/4.08  thf('5', plain,
% 3.86/4.08      (![X13 : $i, X14 : $i]:
% 3.86/4.08         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.86/4.08      inference('cnf', [status(esa)], [t3_subset])).
% 3.86/4.08  thf('6', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.08      inference('sup-', [status(thm)], ['4', '5'])).
% 3.86/4.08  thf('7', plain,
% 3.86/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.08         (~ (r2_hidden @ X0 @ X1)
% 3.86/4.08          | (r2_hidden @ X0 @ X2)
% 3.86/4.08          | ~ (r1_tarski @ X1 @ X2))),
% 3.86/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.86/4.08  thf('8', plain,
% 3.86/4.08      (![X0 : $i]:
% 3.86/4.08         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.08          | ~ (r2_hidden @ X0 @ sk_B))),
% 3.86/4.08      inference('sup-', [status(thm)], ['6', '7'])).
% 3.86/4.08  thf('9', plain,
% 3.86/4.08      (![X0 : $i, X1 : $i]:
% 3.86/4.08         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_B @ X0)) @ X0)
% 3.86/4.08          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ X1)
% 3.86/4.08          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.08             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['3', '8'])).
% 3.86/4.08  thf('10', plain,
% 3.86/4.08      (![X1 : $i, X3 : $i]:
% 3.86/4.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.86/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.86/4.08  thf('11', plain,
% 3.86/4.08      (![X0 : $i]:
% 3.86/4.08         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 3.86/4.08           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.08          | (r2_hidden @ 
% 3.86/4.08             (sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.86/4.08              (k2_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.08             X0)
% 3.86/4.08          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 3.86/4.08             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['9', '10'])).
% 3.86/4.08  thf('12', plain,
% 3.86/4.08      (![X0 : $i]:
% 3.86/4.08         ((r2_hidden @ 
% 3.86/4.08           (sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.86/4.08            (k2_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.08           X0)
% 3.86/4.08          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 3.86/4.08             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('simplify', [status(thm)], ['11'])).
% 3.86/4.08  thf('13', plain,
% 3.86/4.08      ((m1_subset_1 @ sk_C_2 @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('14', plain,
% 3.86/4.08      (![X13 : $i, X14 : $i]:
% 3.86/4.08         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.86/4.08      inference('cnf', [status(esa)], [t3_subset])).
% 3.86/4.08  thf('15', plain,
% 3.86/4.08      ((r1_tarski @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.08      inference('sup-', [status(thm)], ['13', '14'])).
% 3.86/4.08  thf('16', plain,
% 3.86/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.08         (~ (r2_hidden @ X0 @ X1)
% 3.86/4.08          | (r2_hidden @ X0 @ X2)
% 3.86/4.08          | ~ (r1_tarski @ X1 @ X2))),
% 3.86/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.86/4.08  thf('17', plain,
% 3.86/4.08      (![X0 : $i]:
% 3.86/4.08         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.08          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.86/4.08      inference('sup-', [status(thm)], ['15', '16'])).
% 3.86/4.08  thf('18', plain,
% 3.86/4.08      (((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 3.86/4.08         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.08        | (r2_hidden @ 
% 3.86/4.08           (sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.86/4.08            (k2_xboole_0 @ sk_B @ sk_C_2)) @ 
% 3.86/4.08           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['12', '17'])).
% 3.86/4.08  thf('19', plain,
% 3.86/4.08      (![X1 : $i, X3 : $i]:
% 3.86/4.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.86/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.86/4.08  thf('20', plain,
% 3.86/4.08      ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 3.86/4.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.08      inference('clc', [status(thm)], ['18', '19'])).
% 3.86/4.08  thf('21', plain,
% 3.86/4.08      (![X13 : $i, X15 : $i]:
% 3.86/4.08         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 3.86/4.08      inference('cnf', [status(esa)], [t3_subset])).
% 3.86/4.08  thf('22', plain,
% 3.86/4.08      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['20', '21'])).
% 3.86/4.08  thf(d1_tops_2, axiom,
% 3.86/4.08    (![A:$i]:
% 3.86/4.08     ( ( l1_pre_topc @ A ) =>
% 3.86/4.08       ( ![B:$i]:
% 3.86/4.08         ( ( m1_subset_1 @
% 3.86/4.08             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.86/4.08           ( ( v1_tops_2 @ B @ A ) <=>
% 3.86/4.08             ( ![C:$i]:
% 3.86/4.08               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.08                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 3.86/4.08  thf('23', plain,
% 3.86/4.08      (![X16 : $i, X17 : $i]:
% 3.86/4.08         (~ (m1_subset_1 @ X16 @ 
% 3.86/4.08             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 3.86/4.08          | (m1_subset_1 @ (sk_C_1 @ X16 @ X17) @ 
% 3.86/4.08             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.86/4.08          | (v1_tops_2 @ X16 @ X17)
% 3.86/4.08          | ~ (l1_pre_topc @ X17))),
% 3.86/4.08      inference('cnf', [status(esa)], [d1_tops_2])).
% 3.86/4.08  thf('24', plain,
% 3.86/4.08      ((~ (l1_pre_topc @ sk_A)
% 3.86/4.08        | (v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)
% 3.86/4.08        | (m1_subset_1 @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['22', '23'])).
% 3.86/4.08  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('26', plain,
% 3.86/4.08      (((v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)
% 3.86/4.08        | (m1_subset_1 @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('demod', [status(thm)], ['24', '25'])).
% 3.86/4.08  thf('27', plain,
% 3.86/4.08      (~ (v1_tops_2 @ 
% 3.86/4.08          (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_2) @ 
% 3.86/4.08          sk_A)),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('28', plain,
% 3.86/4.08      ((m1_subset_1 @ sk_C_2 @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('29', plain,
% 3.86/4.08      ((m1_subset_1 @ sk_B @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf(redefinition_k4_subset_1, axiom,
% 3.86/4.08    (![A:$i,B:$i,C:$i]:
% 3.86/4.08     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.86/4.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.86/4.08       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.86/4.08  thf('30', plain,
% 3.86/4.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.86/4.08         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.86/4.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 3.86/4.08          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 3.86/4.08      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.86/4.08  thf('31', plain,
% 3.86/4.08      (![X0 : $i]:
% 3.86/4.08         (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 3.86/4.08            = (k2_xboole_0 @ sk_B @ X0))
% 3.86/4.08          | ~ (m1_subset_1 @ X0 @ 
% 3.86/4.08               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['29', '30'])).
% 3.86/4.08  thf('32', plain,
% 3.86/4.08      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_2)
% 3.86/4.08         = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 3.86/4.08      inference('sup-', [status(thm)], ['28', '31'])).
% 3.86/4.08  thf('33', plain, (~ (v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)),
% 3.86/4.08      inference('demod', [status(thm)], ['27', '32'])).
% 3.86/4.08  thf('34', plain,
% 3.86/4.08      ((m1_subset_1 @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.08      inference('clc', [status(thm)], ['26', '33'])).
% 3.86/4.08  thf('35', plain,
% 3.86/4.08      ((m1_subset_1 @ sk_C_2 @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('36', plain,
% 3.86/4.08      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.86/4.08         (~ (m1_subset_1 @ X16 @ 
% 3.86/4.08             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 3.86/4.08          | ~ (v1_tops_2 @ X16 @ X17)
% 3.86/4.08          | ~ (r2_hidden @ X18 @ X16)
% 3.86/4.08          | (v3_pre_topc @ X18 @ X17)
% 3.86/4.08          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.86/4.08          | ~ (l1_pre_topc @ X17))),
% 3.86/4.08      inference('cnf', [status(esa)], [d1_tops_2])).
% 3.86/4.08  thf('37', plain,
% 3.86/4.08      (![X0 : $i]:
% 3.86/4.08         (~ (l1_pre_topc @ sk_A)
% 3.86/4.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.08          | (v3_pre_topc @ X0 @ sk_A)
% 3.86/4.08          | ~ (r2_hidden @ X0 @ sk_C_2)
% 3.86/4.08          | ~ (v1_tops_2 @ sk_C_2 @ sk_A))),
% 3.86/4.08      inference('sup-', [status(thm)], ['35', '36'])).
% 3.86/4.08  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('39', plain, ((v1_tops_2 @ sk_C_2 @ sk_A)),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('40', plain,
% 3.86/4.08      (![X0 : $i]:
% 3.86/4.08         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.08          | (v3_pre_topc @ X0 @ sk_A)
% 3.86/4.08          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.86/4.08      inference('demod', [status(thm)], ['37', '38', '39'])).
% 3.86/4.08  thf('41', plain,
% 3.86/4.08      ((~ (r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_C_2)
% 3.86/4.08        | (v3_pre_topc @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_A))),
% 3.86/4.08      inference('sup-', [status(thm)], ['34', '40'])).
% 3.86/4.08  thf('42', plain,
% 3.86/4.08      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['20', '21'])).
% 3.86/4.08  thf('43', plain,
% 3.86/4.08      (![X16 : $i, X17 : $i]:
% 3.86/4.08         (~ (m1_subset_1 @ X16 @ 
% 3.86/4.08             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 3.86/4.08          | ~ (v3_pre_topc @ (sk_C_1 @ X16 @ X17) @ X17)
% 3.86/4.08          | (v1_tops_2 @ X16 @ X17)
% 3.86/4.08          | ~ (l1_pre_topc @ X17))),
% 3.86/4.08      inference('cnf', [status(esa)], [d1_tops_2])).
% 3.86/4.08  thf('44', plain,
% 3.86/4.08      ((~ (l1_pre_topc @ sk_A)
% 3.86/4.08        | (v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)
% 3.86/4.08        | ~ (v3_pre_topc @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08             sk_A))),
% 3.86/4.08      inference('sup-', [status(thm)], ['42', '43'])).
% 3.86/4.08  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('46', plain,
% 3.86/4.08      (((v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)
% 3.86/4.08        | ~ (v3_pre_topc @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08             sk_A))),
% 3.86/4.08      inference('demod', [status(thm)], ['44', '45'])).
% 3.86/4.08  thf('47', plain, (~ (v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)),
% 3.86/4.08      inference('demod', [status(thm)], ['27', '32'])).
% 3.86/4.08  thf('48', plain,
% 3.86/4.08      (~ (v3_pre_topc @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_A)),
% 3.86/4.08      inference('clc', [status(thm)], ['46', '47'])).
% 3.86/4.08  thf('49', plain,
% 3.86/4.08      (~ (r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_C_2)),
% 3.86/4.08      inference('clc', [status(thm)], ['41', '48'])).
% 3.86/4.08  thf('50', plain,
% 3.86/4.08      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 3.86/4.08        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.08      inference('sup-', [status(thm)], ['20', '21'])).
% 3.86/4.08  thf('51', plain,
% 3.86/4.08      (![X16 : $i, X17 : $i]:
% 3.86/4.08         (~ (m1_subset_1 @ X16 @ 
% 3.86/4.08             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 3.86/4.08          | (r2_hidden @ (sk_C_1 @ X16 @ X17) @ X16)
% 3.86/4.08          | (v1_tops_2 @ X16 @ X17)
% 3.86/4.08          | ~ (l1_pre_topc @ X17))),
% 3.86/4.08      inference('cnf', [status(esa)], [d1_tops_2])).
% 3.86/4.08  thf('52', plain,
% 3.86/4.08      ((~ (l1_pre_topc @ sk_A)
% 3.86/4.08        | (v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)
% 3.86/4.08        | (r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08           (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 3.86/4.08      inference('sup-', [status(thm)], ['50', '51'])).
% 3.86/4.08  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.08  thf('54', plain,
% 3.86/4.08      (((v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)
% 3.86/4.08        | (r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08           (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 3.86/4.08      inference('demod', [status(thm)], ['52', '53'])).
% 3.86/4.08  thf('55', plain, (~ (v1_tops_2 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A)),
% 3.86/4.08      inference('demod', [status(thm)], ['27', '32'])).
% 3.86/4.08  thf('56', plain,
% 3.86/4.08      ((r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.08        (k2_xboole_0 @ sk_B @ sk_C_2))),
% 3.86/4.08      inference('clc', [status(thm)], ['54', '55'])).
% 3.86/4.08  thf('57', plain,
% 3.86/4.08      (![X5 : $i, X7 : $i, X8 : $i]:
% 3.86/4.09         ((r2_hidden @ X8 @ X5)
% 3.86/4.09          | (r2_hidden @ X8 @ X7)
% 3.86/4.09          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 3.86/4.09      inference('simplify', [status(thm)], ['1'])).
% 3.86/4.09  thf('58', plain,
% 3.86/4.09      (((r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_B)
% 3.86/4.09        | (r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_C_2))),
% 3.86/4.09      inference('sup-', [status(thm)], ['56', '57'])).
% 3.86/4.09  thf('59', plain,
% 3.86/4.09      ((m1_subset_1 @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ 
% 3.86/4.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.09      inference('clc', [status(thm)], ['26', '33'])).
% 3.86/4.09  thf('60', plain,
% 3.86/4.09      ((m1_subset_1 @ sk_B @ 
% 3.86/4.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.86/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.09  thf('61', plain,
% 3.86/4.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.86/4.09         (~ (m1_subset_1 @ X16 @ 
% 3.86/4.09             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 3.86/4.09          | ~ (v1_tops_2 @ X16 @ X17)
% 3.86/4.09          | ~ (r2_hidden @ X18 @ X16)
% 3.86/4.09          | (v3_pre_topc @ X18 @ X17)
% 3.86/4.09          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 3.86/4.09          | ~ (l1_pre_topc @ X17))),
% 3.86/4.09      inference('cnf', [status(esa)], [d1_tops_2])).
% 3.86/4.09  thf('62', plain,
% 3.86/4.09      (![X0 : $i]:
% 3.86/4.09         (~ (l1_pre_topc @ sk_A)
% 3.86/4.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.09          | (v3_pre_topc @ X0 @ sk_A)
% 3.86/4.09          | ~ (r2_hidden @ X0 @ sk_B)
% 3.86/4.09          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 3.86/4.09      inference('sup-', [status(thm)], ['60', '61'])).
% 3.86/4.09  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.09  thf('64', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 3.86/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.09  thf('65', plain,
% 3.86/4.09      (![X0 : $i]:
% 3.86/4.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.09          | (v3_pre_topc @ X0 @ sk_A)
% 3.86/4.09          | ~ (r2_hidden @ X0 @ sk_B))),
% 3.86/4.09      inference('demod', [status(thm)], ['62', '63', '64'])).
% 3.86/4.09  thf('66', plain,
% 3.86/4.09      ((~ (r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_B)
% 3.86/4.09        | (v3_pre_topc @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_A))),
% 3.86/4.09      inference('sup-', [status(thm)], ['59', '65'])).
% 3.86/4.09  thf('67', plain,
% 3.86/4.09      (~ (v3_pre_topc @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_A)),
% 3.86/4.09      inference('clc', [status(thm)], ['46', '47'])).
% 3.86/4.09  thf('68', plain,
% 3.86/4.09      (~ (r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_B)),
% 3.86/4.09      inference('clc', [status(thm)], ['66', '67'])).
% 3.86/4.09  thf('69', plain,
% 3.86/4.09      ((r2_hidden @ (sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_A) @ sk_C_2)),
% 3.86/4.09      inference('clc', [status(thm)], ['58', '68'])).
% 3.86/4.09  thf('70', plain, ($false), inference('demod', [status(thm)], ['49', '69'])).
% 3.86/4.09  
% 3.86/4.09  % SZS output end Refutation
% 3.86/4.09  
% 3.86/4.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
