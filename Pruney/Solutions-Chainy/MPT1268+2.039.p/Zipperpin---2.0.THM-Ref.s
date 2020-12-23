%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ymv13UynH

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:21 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 801 expanded)
%              Number of leaves         :   28 ( 224 expanded)
%              Depth                    :   23
%              Number of atoms          : 1265 (11680 expanded)
%              Number of equality atoms :   58 ( 470 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('11',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('13',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X36 @ sk_A )
      | ~ ( r1_tarski @ X36 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X36: $i] :
        ( ( X36 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X36 @ sk_A )
        | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X36: $i] :
        ( ( X36 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X36 @ sk_A )
        | ~ ( r1_tarski @ X36 @ sk_B ) )
   <= ! [X36: $i] :
        ( ( X36 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X36 @ sk_A )
        | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X36: $i] :
        ( ( X36 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X36 @ sk_A )
        | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('37',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X36: $i] :
        ( ( X36 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X36 @ sk_A )
        | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X35 @ X34 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X36: $i] :
        ( ( X36 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X36 @ sk_A )
        | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X36: $i] :
        ( ( X36 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X36 @ sk_A )
        | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('50',plain,
    ( ~ ! [X36: $i] :
          ( ( X36 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X36 @ sk_A )
          | ~ ( r1_tarski @ X36 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('52',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['18','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['16','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ k1_xboole_0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','53'])).

thf('55',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('58',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','50','57'])).

thf('59',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ k1_xboole_0 ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ k1_xboole_0 ) @ sk_C_1 )
    | ( sk_C_1
      = ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ k1_xboole_0 ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','58'])).

thf('66',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ k1_xboole_0 ) @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['18','50','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['68'])).

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

thf('79',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X30 )
      | ( ( k1_tops_1 @ X30 @ X31 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('80',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( l1_pre_topc @ X30 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( v3_pre_topc @ X31 @ X30 )
        | ( ( k1_tops_1 @ X30 @ X31 )
          = X31 ) )
   <= ! [X30: $i,X31: $i] :
        ( ~ ( l1_pre_topc @ X30 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( v3_pre_topc @ X31 @ X30 )
        | ( ( k1_tops_1 @ X30 @ X31 )
          = X31 ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X30 )
      | ( ( k1_tops_1 @ X30 @ X31 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('83',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
        | ~ ( l1_pre_topc @ X33 )
        | ~ ( v2_pre_topc @ X33 ) )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
        | ~ ( l1_pre_topc @ X33 )
        | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
        | ~ ( l1_pre_topc @ X33 )
        | ~ ( v2_pre_topc @ X33 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ~ ! [X32: $i,X33: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
        | ~ ( l1_pre_topc @ X33 )
        | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ! [X30: $i,X31: $i] :
        ( ~ ( l1_pre_topc @ X30 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
        | ~ ( v3_pre_topc @ X31 @ X30 )
        | ( ( k1_tops_1 @ X30 @ X31 )
          = X31 ) )
    | ! [X32: $i,X33: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
        | ~ ( l1_pre_topc @ X33 )
        | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(split,[status(esa)],['82'])).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X30 )
      | ( ( k1_tops_1 @ X30 @ X31 )
        = X31 ) ) ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X30 )
      | ( ( k1_tops_1 @ X30 @ X31 )
        = X31 ) ) ),
    inference(simpl_trail,[status(thm)],['80','89'])).

thf('91',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
      = sk_C_1 )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['77','93'])).

thf('95',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('96',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['18','50','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['18','50','70'])).

thf('98',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['94','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','98'])).

thf('100',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','99'])).

thf('101',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('102',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['18','50','51'])).

thf('103',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(simpl_trail,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tops_1 @ X34 @ X35 )
      | ( ( k1_tops_1 @ X35 @ X34 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['18','50'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103','112'])).

thf('114',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('116',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ X0 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['66','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('122',plain,(
    $false ),
    inference('sup-',[status(thm)],['120','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ymv13UynH
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.69/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.86  % Solved by: fo/fo7.sh
% 0.69/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.86  % done 1050 iterations in 0.414s
% 0.69/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.86  % SZS output start Refutation
% 0.69/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.86  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.69/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.69/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.86  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.69/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.86  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.69/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.86  thf(d5_xboole_0, axiom,
% 0.69/0.86    (![A:$i,B:$i,C:$i]:
% 0.69/0.86     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.69/0.86       ( ![D:$i]:
% 0.69/0.86         ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.86           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.69/0.86  thf('0', plain,
% 0.69/0.86      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.69/0.86         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.69/0.86          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.69/0.86          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.69/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.86  thf(t3_boole, axiom,
% 0.69/0.86    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.86  thf('1', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.69/0.86      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.86  thf('2', plain,
% 0.69/0.86      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X8 @ X7)
% 0.69/0.86          | ~ (r2_hidden @ X8 @ X6)
% 0.69/0.86          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.69/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.86  thf('3', plain,
% 0.69/0.86      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X8 @ X6)
% 0.69/0.86          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.69/0.86      inference('simplify', [status(thm)], ['2'])).
% 0.69/0.86  thf('4', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['1', '3'])).
% 0.69/0.86  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.86      inference('condensation', [status(thm)], ['4'])).
% 0.69/0.86  thf('6', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.69/0.86          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['0', '5'])).
% 0.69/0.86  thf('7', plain,
% 0.69/0.86      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.69/0.86         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.69/0.86          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.69/0.86          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.69/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.86  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.86      inference('condensation', [status(thm)], ['4'])).
% 0.69/0.86  thf('9', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.69/0.86          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['7', '8'])).
% 0.69/0.86  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.86      inference('condensation', [status(thm)], ['4'])).
% 0.69/0.86  thf('11', plain,
% 0.69/0.86      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.86  thf('12', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.69/0.86          | ((X1) = (k1_xboole_0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['6', '11'])).
% 0.69/0.86  thf(t86_tops_1, conjecture,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.69/0.86             ( ![C:$i]:
% 0.69/0.86               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.69/0.86                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.86    (~( ![A:$i]:
% 0.69/0.86        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.86          ( ![B:$i]:
% 0.69/0.86            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86              ( ( v2_tops_1 @ B @ A ) <=>
% 0.69/0.86                ( ![C:$i]:
% 0.69/0.86                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.69/0.86                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.69/0.86    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.69/0.86  thf('13', plain,
% 0.69/0.86      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('14', plain,
% 0.69/0.86      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.69/0.86      inference('split', [status(esa)], ['13'])).
% 0.69/0.86  thf(d3_tarski, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( r1_tarski @ A @ B ) <=>
% 0.69/0.86       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.69/0.86  thf('15', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.86          | (r2_hidden @ X0 @ X2)
% 0.69/0.86          | ~ (r1_tarski @ X1 @ X2))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.86  thf('16', plain,
% 0.69/0.86      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.69/0.86         <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['14', '15'])).
% 0.69/0.86  thf('17', plain,
% 0.69/0.86      (![X36 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86          | ((X36) = (k1_xboole_0))
% 0.69/0.86          | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86          | ~ (r1_tarski @ X36 @ sk_B)
% 0.69/0.86          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('18', plain,
% 0.69/0.86      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.69/0.86       (![X36 : $i]:
% 0.69/0.86          (((X36) = (k1_xboole_0))
% 0.69/0.86           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86           | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86           | ~ (r1_tarski @ X36 @ sk_B)))),
% 0.69/0.86      inference('split', [status(esa)], ['17'])).
% 0.69/0.86  thf('19', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t3_subset, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.86  thf('20', plain,
% 0.69/0.86      (![X20 : $i, X21 : $i]:
% 0.69/0.86         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.69/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.86  thf('21', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.86  thf('22', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t44_tops_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.69/0.86  thf('23', plain,
% 0.69/0.86      (![X25 : $i, X26 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.69/0.86          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ X25)
% 0.69/0.86          | ~ (l1_pre_topc @ X26))),
% 0.69/0.86      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.69/0.86  thf('24', plain,
% 0.69/0.86      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.69/0.86      inference('sup-', [status(thm)], ['22', '23'])).
% 0.69/0.86  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('26', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.69/0.86      inference('demod', [status(thm)], ['24', '25'])).
% 0.69/0.86  thf(t1_xboole_1, axiom,
% 0.69/0.86    (![A:$i,B:$i,C:$i]:
% 0.69/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.69/0.86       ( r1_tarski @ A @ C ) ))).
% 0.69/0.86  thf('27', plain,
% 0.69/0.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.86         (~ (r1_tarski @ X12 @ X13)
% 0.69/0.86          | ~ (r1_tarski @ X13 @ X14)
% 0.69/0.86          | (r1_tarski @ X12 @ X14))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.69/0.86  thf('28', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.69/0.86          | ~ (r1_tarski @ sk_B @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.86  thf('29', plain,
% 0.69/0.86      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['21', '28'])).
% 0.69/0.86  thf('30', plain,
% 0.69/0.86      (![X20 : $i, X22 : $i]:
% 0.69/0.86         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.69/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.86  thf('31', plain,
% 0.69/0.86      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.86  thf('32', plain,
% 0.69/0.86      ((![X36 : $i]:
% 0.69/0.86          (((X36) = (k1_xboole_0))
% 0.69/0.86           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86           | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86           | ~ (r1_tarski @ X36 @ sk_B)))
% 0.69/0.86         <= ((![X36 : $i]:
% 0.69/0.86                (((X36) = (k1_xboole_0))
% 0.69/0.86                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86                 | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86                 | ~ (r1_tarski @ X36 @ sk_B))))),
% 0.69/0.86      inference('split', [status(esa)], ['17'])).
% 0.69/0.86  thf('33', plain,
% 0.69/0.86      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.69/0.86         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.69/0.86         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.69/0.86         <= ((![X36 : $i]:
% 0.69/0.86                (((X36) = (k1_xboole_0))
% 0.69/0.86                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86                 | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86                 | ~ (r1_tarski @ X36 @ sk_B))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['31', '32'])).
% 0.69/0.86  thf('34', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.69/0.86      inference('demod', [status(thm)], ['24', '25'])).
% 0.69/0.86  thf('35', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(fc9_tops_1, axiom,
% 0.69/0.86    (![A:$i,B:$i]:
% 0.69/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.69/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.86       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.69/0.86  thf('36', plain,
% 0.69/0.86      (![X23 : $i, X24 : $i]:
% 0.69/0.86         (~ (l1_pre_topc @ X23)
% 0.69/0.86          | ~ (v2_pre_topc @ X23)
% 0.69/0.86          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.69/0.86          | (v3_pre_topc @ (k1_tops_1 @ X23 @ X24) @ X23))),
% 0.69/0.86      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.69/0.86  thf('37', plain,
% 0.69/0.86      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.69/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.86  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('40', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.69/0.86      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.69/0.86  thf('41', plain,
% 0.69/0.86      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.69/0.86         <= ((![X36 : $i]:
% 0.69/0.86                (((X36) = (k1_xboole_0))
% 0.69/0.86                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86                 | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86                 | ~ (r1_tarski @ X36 @ sk_B))))),
% 0.69/0.86      inference('demod', [status(thm)], ['33', '34', '40'])).
% 0.69/0.86  thf('42', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf(t84_tops_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.69/0.86             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.69/0.86  thf('43', plain,
% 0.69/0.86      (![X34 : $i, X35 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.69/0.86          | ((k1_tops_1 @ X35 @ X34) != (k1_xboole_0))
% 0.69/0.86          | (v2_tops_1 @ X34 @ X35)
% 0.69/0.86          | ~ (l1_pre_topc @ X35))),
% 0.69/0.86      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.69/0.86  thf('44', plain,
% 0.69/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.86        | (v2_tops_1 @ sk_B @ sk_A)
% 0.69/0.86        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['42', '43'])).
% 0.69/0.86  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('46', plain,
% 0.69/0.86      (((v2_tops_1 @ sk_B @ sk_A)
% 0.69/0.86        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.69/0.86  thf('47', plain,
% 0.69/0.86      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.69/0.86         <= ((![X36 : $i]:
% 0.69/0.86                (((X36) = (k1_xboole_0))
% 0.69/0.86                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86                 | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86                 | ~ (r1_tarski @ X36 @ sk_B))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['41', '46'])).
% 0.69/0.86  thf('48', plain,
% 0.69/0.86      (((v2_tops_1 @ sk_B @ sk_A))
% 0.69/0.86         <= ((![X36 : $i]:
% 0.69/0.86                (((X36) = (k1_xboole_0))
% 0.69/0.86                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86                 | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86                 | ~ (r1_tarski @ X36 @ sk_B))))),
% 0.69/0.86      inference('simplify', [status(thm)], ['47'])).
% 0.69/0.86  thf('49', plain,
% 0.69/0.86      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.69/0.86      inference('split', [status(esa)], ['13'])).
% 0.69/0.86  thf('50', plain,
% 0.69/0.86      (~
% 0.69/0.86       (![X36 : $i]:
% 0.69/0.86          (((X36) = (k1_xboole_0))
% 0.69/0.86           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86           | ~ (v3_pre_topc @ X36 @ sk_A)
% 0.69/0.86           | ~ (r1_tarski @ X36 @ sk_B))) | 
% 0.69/0.86       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['48', '49'])).
% 0.69/0.86  thf('51', plain,
% 0.69/0.86      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('split', [status(esa)], ['13'])).
% 0.69/0.86  thf('52', plain, (((r1_tarski @ sk_C_1 @ sk_B))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['18', '50', '51'])).
% 0.69/0.86  thf('53', plain,
% 0.69/0.86      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['16', '52'])).
% 0.69/0.86  thf('54', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (((sk_C_1) = (k1_xboole_0))
% 0.69/0.86          | (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ k1_xboole_0) @ sk_B))),
% 0.69/0.86      inference('sup-', [status(thm)], ['12', '53'])).
% 0.69/0.86  thf('55', plain,
% 0.69/0.86      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('56', plain,
% 0.69/0.86      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.69/0.86      inference('split', [status(esa)], ['55'])).
% 0.69/0.86  thf('57', plain,
% 0.69/0.86      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('split', [status(esa)], ['55'])).
% 0.69/0.86  thf('58', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['18', '50', '57'])).
% 0.69/0.86  thf('59', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['56', '58'])).
% 0.69/0.86  thf('60', plain,
% 0.69/0.86      (![X0 : $i]: (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ k1_xboole_0) @ sk_B)),
% 0.69/0.86      inference('simplify_reflect-', [status(thm)], ['54', '59'])).
% 0.69/0.86  thf('61', plain,
% 0.69/0.86      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.69/0.86         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.69/0.86          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.69/0.86          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.69/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.86  thf('62', plain,
% 0.69/0.86      (((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ k1_xboole_0) @ sk_C_1)
% 0.69/0.86        | ((sk_C_1) = (k4_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['60', '61'])).
% 0.69/0.86  thf('63', plain,
% 0.69/0.86      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.86  thf('64', plain,
% 0.69/0.86      (((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ k1_xboole_0) @ sk_C_1)
% 0.69/0.86        | ((sk_C_1) = (k1_xboole_0)))),
% 0.69/0.86      inference('demod', [status(thm)], ['62', '63'])).
% 0.69/0.86  thf('65', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['56', '58'])).
% 0.69/0.86  thf('66', plain,
% 0.69/0.86      ((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ k1_xboole_0) @ sk_C_1)),
% 0.69/0.86      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.69/0.86  thf('67', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('68', plain,
% 0.69/0.86      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('69', plain,
% 0.69/0.86      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.69/0.86         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.69/0.86      inference('split', [status(esa)], ['68'])).
% 0.69/0.86  thf('70', plain,
% 0.69/0.86      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.69/0.86       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('split', [status(esa)], ['68'])).
% 0.69/0.86  thf('71', plain,
% 0.69/0.86      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['18', '50', '70'])).
% 0.69/0.86  thf('72', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 0.69/0.86  thf(t48_tops_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( l1_pre_topc @ A ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86               ( ( r1_tarski @ B @ C ) =>
% 0.69/0.86                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf('73', plain,
% 0.69/0.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.69/0.86          | ~ (r1_tarski @ X27 @ X29)
% 0.69/0.86          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ (k1_tops_1 @ X28 @ X29))
% 0.69/0.86          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.69/0.86          | ~ (l1_pre_topc @ X28))),
% 0.69/0.86      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.69/0.86  thf('74', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (l1_pre_topc @ sk_A)
% 0.69/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.69/0.86          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['72', '73'])).
% 0.69/0.86  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('76', plain,
% 0.69/0.86      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('77', plain,
% 0.69/0.86      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.69/0.86      inference('split', [status(esa)], ['76'])).
% 0.69/0.86  thf('78', plain,
% 0.69/0.86      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.69/0.86         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.69/0.86      inference('split', [status(esa)], ['68'])).
% 0.69/0.86  thf(t55_tops_1, axiom,
% 0.69/0.86    (![A:$i]:
% 0.69/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.86       ( ![B:$i]:
% 0.69/0.86         ( ( l1_pre_topc @ B ) =>
% 0.69/0.86           ( ![C:$i]:
% 0.69/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.86               ( ![D:$i]:
% 0.69/0.86                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.69/0.86                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.69/0.86                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.69/0.86                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.69/0.86                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.86  thf('79', plain,
% 0.69/0.86      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.86         (~ (l1_pre_topc @ X30)
% 0.69/0.86          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.86          | ~ (v3_pre_topc @ X31 @ X30)
% 0.69/0.86          | ((k1_tops_1 @ X30 @ X31) = (X31))
% 0.69/0.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.86          | ~ (l1_pre_topc @ X33)
% 0.69/0.86          | ~ (v2_pre_topc @ X33))),
% 0.69/0.86      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.69/0.86  thf('80', plain,
% 0.69/0.86      ((![X30 : $i, X31 : $i]:
% 0.69/0.86          (~ (l1_pre_topc @ X30)
% 0.69/0.86           | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.86           | ~ (v3_pre_topc @ X31 @ X30)
% 0.69/0.86           | ((k1_tops_1 @ X30 @ X31) = (X31))))
% 0.69/0.86         <= ((![X30 : $i, X31 : $i]:
% 0.69/0.86                (~ (l1_pre_topc @ X30)
% 0.69/0.86                 | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.86                 | ~ (v3_pre_topc @ X31 @ X30)
% 0.69/0.86                 | ((k1_tops_1 @ X30 @ X31) = (X31)))))),
% 0.69/0.86      inference('split', [status(esa)], ['79'])).
% 0.69/0.86  thf('81', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('82', plain,
% 0.69/0.86      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.86         (~ (l1_pre_topc @ X30)
% 0.69/0.86          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.86          | ~ (v3_pre_topc @ X31 @ X30)
% 0.69/0.86          | ((k1_tops_1 @ X30 @ X31) = (X31))
% 0.69/0.86          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.86          | ~ (l1_pre_topc @ X33)
% 0.69/0.86          | ~ (v2_pre_topc @ X33))),
% 0.69/0.86      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.69/0.86  thf('83', plain,
% 0.69/0.86      ((![X32 : $i, X33 : $i]:
% 0.69/0.86          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.86           | ~ (l1_pre_topc @ X33)
% 0.69/0.86           | ~ (v2_pre_topc @ X33)))
% 0.69/0.86         <= ((![X32 : $i, X33 : $i]:
% 0.69/0.86                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.86                 | ~ (l1_pre_topc @ X33)
% 0.69/0.86                 | ~ (v2_pre_topc @ X33))))),
% 0.69/0.86      inference('split', [status(esa)], ['82'])).
% 0.69/0.86  thf('84', plain,
% 0.69/0.86      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.69/0.86         <= ((![X32 : $i, X33 : $i]:
% 0.69/0.86                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.86                 | ~ (l1_pre_topc @ X33)
% 0.69/0.86                 | ~ (v2_pre_topc @ X33))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['81', '83'])).
% 0.69/0.86  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('87', plain,
% 0.69/0.86      (~
% 0.69/0.86       (![X32 : $i, X33 : $i]:
% 0.69/0.86          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.86           | ~ (l1_pre_topc @ X33)
% 0.69/0.86           | ~ (v2_pre_topc @ X33)))),
% 0.69/0.86      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.69/0.86  thf('88', plain,
% 0.69/0.86      ((![X30 : $i, X31 : $i]:
% 0.69/0.86          (~ (l1_pre_topc @ X30)
% 0.69/0.86           | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.86           | ~ (v3_pre_topc @ X31 @ X30)
% 0.69/0.86           | ((k1_tops_1 @ X30 @ X31) = (X31)))) | 
% 0.69/0.86       (![X32 : $i, X33 : $i]:
% 0.69/0.86          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.86           | ~ (l1_pre_topc @ X33)
% 0.69/0.86           | ~ (v2_pre_topc @ X33)))),
% 0.69/0.86      inference('split', [status(esa)], ['82'])).
% 0.69/0.86  thf('89', plain,
% 0.69/0.86      ((![X30 : $i, X31 : $i]:
% 0.69/0.86          (~ (l1_pre_topc @ X30)
% 0.69/0.86           | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.86           | ~ (v3_pre_topc @ X31 @ X30)
% 0.69/0.86           | ((k1_tops_1 @ X30 @ X31) = (X31))))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.69/0.86  thf('90', plain,
% 0.69/0.86      (![X30 : $i, X31 : $i]:
% 0.69/0.86         (~ (l1_pre_topc @ X30)
% 0.69/0.86          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.86          | ~ (v3_pre_topc @ X31 @ X30)
% 0.69/0.86          | ((k1_tops_1 @ X30 @ X31) = (X31)))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['80', '89'])).
% 0.69/0.86  thf('91', plain,
% 0.69/0.86      (((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))
% 0.69/0.86         | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.69/0.86         | ~ (l1_pre_topc @ sk_A)))
% 0.69/0.86         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['78', '90'])).
% 0.69/0.86  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('93', plain,
% 0.69/0.86      (((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))
% 0.69/0.86         | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 0.69/0.86         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.69/0.86      inference('demod', [status(thm)], ['91', '92'])).
% 0.69/0.86  thf('94', plain,
% 0.69/0.86      ((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1)))
% 0.69/0.86         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.69/0.86             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.69/0.86      inference('sup-', [status(thm)], ['77', '93'])).
% 0.69/0.86  thf('95', plain,
% 0.69/0.86      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('split', [status(esa)], ['76'])).
% 0.69/0.86  thf('96', plain, (((v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['18', '50', '95'])).
% 0.69/0.86  thf('97', plain,
% 0.69/0.86      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['18', '50', '70'])).
% 0.69/0.86  thf('98', plain, (((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['94', '96', '97'])).
% 0.69/0.86  thf('99', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.86          | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.69/0.86          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.69/0.86      inference('demod', [status(thm)], ['74', '75', '98'])).
% 0.69/0.86  thf('100', plain,
% 0.69/0.86      ((~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.69/0.86        | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['67', '99'])).
% 0.69/0.86  thf('101', plain,
% 0.69/0.86      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.69/0.86      inference('split', [status(esa)], ['13'])).
% 0.69/0.86  thf('102', plain, (((r1_tarski @ sk_C_1 @ sk_B))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['18', '50', '51'])).
% 0.69/0.86  thf('103', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['101', '102'])).
% 0.69/0.86  thf('104', plain,
% 0.69/0.86      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.69/0.86      inference('split', [status(esa)], ['17'])).
% 0.69/0.86  thf('105', plain,
% 0.69/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('106', plain,
% 0.69/0.86      (![X34 : $i, X35 : $i]:
% 0.69/0.86         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.69/0.86          | ~ (v2_tops_1 @ X34 @ X35)
% 0.69/0.86          | ((k1_tops_1 @ X35 @ X34) = (k1_xboole_0))
% 0.69/0.86          | ~ (l1_pre_topc @ X35))),
% 0.69/0.86      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.69/0.86  thf('107', plain,
% 0.69/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.86        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.69/0.86        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('sup-', [status(thm)], ['105', '106'])).
% 0.69/0.86  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.86  thf('109', plain,
% 0.69/0.86      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.69/0.86        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('demod', [status(thm)], ['107', '108'])).
% 0.69/0.86  thf('110', plain,
% 0.69/0.86      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.69/0.86         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.69/0.86      inference('sup-', [status(thm)], ['104', '109'])).
% 0.69/0.86  thf('111', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.69/0.86      inference('sat_resolution*', [status(thm)], ['18', '50'])).
% 0.69/0.86  thf('112', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.69/0.86      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.69/0.86  thf('113', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.69/0.86      inference('demod', [status(thm)], ['100', '103', '112'])).
% 0.69/0.86  thf('114', plain,
% 0.69/0.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.69/0.86         (~ (r1_tarski @ X12 @ X13)
% 0.69/0.86          | ~ (r1_tarski @ X13 @ X14)
% 0.69/0.86          | (r1_tarski @ X12 @ X14))),
% 0.69/0.86      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.69/0.86  thf('115', plain,
% 0.69/0.86      (![X0 : $i]:
% 0.69/0.86         ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.69/0.86      inference('sup-', [status(thm)], ['113', '114'])).
% 0.69/0.86  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.69/0.86  thf('116', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.69/0.86      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.86  thf('117', plain, (![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)),
% 0.69/0.86      inference('demod', [status(thm)], ['115', '116'])).
% 0.69/0.86  thf('118', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.86         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.86          | (r2_hidden @ X0 @ X2)
% 0.69/0.86          | ~ (r1_tarski @ X1 @ X2))),
% 0.69/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.86  thf('119', plain,
% 0.69/0.86      (![X0 : $i, X1 : $i]:
% 0.69/0.86         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_C_1))),
% 0.69/0.86      inference('sup-', [status(thm)], ['117', '118'])).
% 0.69/0.86  thf('120', plain,
% 0.69/0.86      (![X0 : $i]: (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ k1_xboole_0) @ X0)),
% 0.69/0.86      inference('sup-', [status(thm)], ['66', '119'])).
% 0.69/0.86  thf('121', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.86      inference('condensation', [status(thm)], ['4'])).
% 0.69/0.86  thf('122', plain, ($false), inference('sup-', [status(thm)], ['120', '121'])).
% 0.69/0.86  
% 0.69/0.86  % SZS output end Refutation
% 0.69/0.86  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
