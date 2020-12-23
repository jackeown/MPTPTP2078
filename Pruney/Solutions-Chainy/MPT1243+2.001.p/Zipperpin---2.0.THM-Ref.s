%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZP3wbH3ZQC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:09 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 466 expanded)
%              Number of leaves         :   25 ( 128 expanded)
%              Depth                    :   21
%              Number of atoms          : 1112 (6194 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(t57_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ B )
              <=> ? [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                    & ( v3_pre_topc @ D @ A )
                    & ( r1_tarski @ D @ B )
                    & ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ D )
        & ( r1_tarski @ D @ B )
        & ( v3_pre_topc @ D @ A )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ B )
              <=> ? [D: $i] :
                    ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ B )
                <=> ? [D: $i] :
                      ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[zf_stmt_2])).

thf('0',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
      | ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A )
   <= ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_D_2 )
   <= ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A )
   <= ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_B )
   <= ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_D_2 ) )
   <= ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
   <= ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A )
   <= ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ! [X23: $i] :
        ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X23: $i] :
        ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ! [X23: $i] :
          ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X23: $i] :
        ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 @ sk_B @ sk_A )
      | ( r2_hidden @ X21 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X19 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ sk_B @ X0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X1 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( zip_tseitin_0 @ sk_B @ X0 @ sk_B @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( zip_tseitin_0 @ sk_B @ sk_C_1 @ sk_B @ sk_A )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,
    ( ! [X23: $i] :
        ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X23: $i] :
        ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ! [X23: $i] :
          ~ ( zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31'])).

thf('33',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('36',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X10 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('54',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['52','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','53'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v3_pre_topc @ X16 @ X18 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v3_pre_topc @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','53'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X22: $i] :
        ( ~ ( r2_hidden @ X22 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X22 ) @ X22 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','53'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X11 )
      | ~ ( v3_pre_topc @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X13 @ ( k1_tops_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['60','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','86'])).

thf('88',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['39','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['33','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZP3wbH3ZQC
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 1219 iterations in 0.357s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.81  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.61/0.81  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.61/0.81  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.61/0.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.81  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.61/0.81  thf(t57_tops_1, conjecture,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.81           ( ( v3_pre_topc @ B @ A ) <=>
% 0.61/0.81             ( ![C:$i]:
% 0.61/0.81               ( ( r2_hidden @ C @ B ) <=>
% 0.61/0.81                 ( ?[D:$i]:
% 0.61/0.81                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.61/0.81                     ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ B ) & 
% 0.61/0.81                     ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.61/0.81  thf(zf_stmt_1, axiom,
% 0.61/0.81    (![D:$i,C:$i,B:$i,A:$i]:
% 0.61/0.81     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.61/0.81       ( ( r2_hidden @ C @ D ) & ( r1_tarski @ D @ B ) & 
% 0.61/0.81         ( v3_pre_topc @ D @ A ) & 
% 0.61/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_2, conjecture,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.81           ( ( v3_pre_topc @ B @ A ) <=>
% 0.61/0.81             ( ![C:$i]:
% 0.61/0.81               ( ( r2_hidden @ C @ B ) <=>
% 0.61/0.81                 ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_3, negated_conjecture,
% 0.61/0.81    (~( ![A:$i]:
% 0.61/0.81        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.81          ( ![B:$i]:
% 0.61/0.81            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.81              ( ( v3_pre_topc @ B @ A ) <=>
% 0.61/0.81                ( ![C:$i]:
% 0.61/0.81                  ( ( r2_hidden @ C @ B ) <=>
% 0.61/0.81                    ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [zf_stmt_2])).
% 0.61/0.81  thf('0', plain,
% 0.61/0.81      (![X23 : $i]:
% 0.61/0.81         (~ (r2_hidden @ sk_C_1 @ sk_B)
% 0.61/0.81          | ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A)
% 0.61/0.81          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('1', plain,
% 0.61/0.81      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf('2', plain,
% 0.61/0.81      (((r2_hidden @ sk_C_1 @ sk_B)
% 0.61/0.81        | (zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)
% 0.61/0.81        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('3', plain,
% 0.61/0.81      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 0.61/0.81       ((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A))),
% 0.61/0.81      inference('split', [status(esa)], ['2'])).
% 0.61/0.81  thf('4', plain,
% 0.61/0.81      (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A))
% 0.61/0.81         <= (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('split', [status(esa)], ['2'])).
% 0.61/0.81  thf('5', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.81         ((r2_hidden @ X15 @ X16) | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('6', plain,
% 0.61/0.81      (((r2_hidden @ sk_C_1 @ sk_D_2))
% 0.61/0.81         <= (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.81  thf('7', plain,
% 0.61/0.81      (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A))
% 0.61/0.81         <= (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('split', [status(esa)], ['2'])).
% 0.61/0.81  thf('8', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.81         ((r1_tarski @ X16 @ X17) | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (((r1_tarski @ sk_D_2 @ sk_B))
% 0.61/0.81         <= (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.61/0.81  thf(d3_tarski, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.81          | (r2_hidden @ X0 @ X2)
% 0.61/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.61/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_D_2)))
% 0.61/0.81         <= (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (((r2_hidden @ sk_C_1 @ sk_B))
% 0.61/0.81         <= (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['6', '11'])).
% 0.61/0.81  thf('13', plain,
% 0.61/0.81      ((~ (r2_hidden @ sk_C_1 @ sk_B)) <= (~ ((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      (~ ((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.61/0.81       ((r2_hidden @ sk_C_1 @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A))
% 0.61/0.81         <= (((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('split', [status(esa)], ['2'])).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      ((![X23 : $i]: ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A))
% 0.61/0.81         <= ((![X23 : $i]: ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf('17', plain,
% 0.61/0.81      (~ ((zip_tseitin_0 @ sk_D_2 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.61/0.81       ~ (![X23 : $i]: ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.81  thf('18', plain,
% 0.61/0.81      ((![X23 : $i]: ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.61/0.81       ~ ((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.61/0.81      inference('split', [status(esa)], ['2'])).
% 0.61/0.81  thf(d10_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.81  thf('21', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.61/0.81      inference('simplify', [status(thm)], ['20'])).
% 0.61/0.81  thf('22', plain,
% 0.61/0.81      (![X20 : $i, X21 : $i]:
% 0.61/0.81         (~ (zip_tseitin_0 @ X20 @ X21 @ sk_B @ sk_A)
% 0.61/0.81          | (r2_hidden @ X21 @ sk_B)
% 0.61/0.81          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('23', plain,
% 0.61/0.81      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.81      inference('split', [status(esa)], ['22'])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.61/0.81         ((zip_tseitin_0 @ X16 @ X15 @ X17 @ X19)
% 0.61/0.81          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.61/0.81          | ~ (v3_pre_topc @ X16 @ X19)
% 0.61/0.81          | ~ (r1_tarski @ X16 @ X17)
% 0.61/0.81          | ~ (r2_hidden @ X15 @ X16))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ sk_B)
% 0.61/0.81          | ~ (r1_tarski @ sk_B @ X1)
% 0.61/0.81          | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.61/0.81          | (zip_tseitin_0 @ sk_B @ X0 @ X1 @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.81  thf('27', plain,
% 0.61/0.81      ((![X0 : $i, X1 : $i]:
% 0.61/0.81          ((zip_tseitin_0 @ sk_B @ X1 @ X0 @ sk_A)
% 0.61/0.81           | ~ (r1_tarski @ sk_B @ X0)
% 0.61/0.81           | ~ (r2_hidden @ X1 @ sk_B)))
% 0.61/0.81         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['23', '26'])).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          (~ (r2_hidden @ X0 @ sk_B)
% 0.61/0.81           | (zip_tseitin_0 @ sk_B @ X0 @ sk_B @ sk_A)))
% 0.61/0.81         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['21', '27'])).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (((zip_tseitin_0 @ sk_B @ sk_C_1 @ sk_B @ sk_A))
% 0.61/0.81         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['19', '28'])).
% 0.61/0.81  thf('30', plain,
% 0.61/0.81      ((![X23 : $i]: ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A))
% 0.61/0.81         <= ((![X23 : $i]: ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf('31', plain,
% 0.61/0.81      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 0.61/0.81       ~ (![X23 : $i]: ~ (zip_tseitin_0 @ X23 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.61/0.81       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.81  thf('32', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('sat_resolution*', [status(thm)], ['3', '14', '17', '18', '31'])).
% 0.61/0.81  thf('33', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.61/0.81      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.61/0.81  thf('34', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf(fc9_tops_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.61/0.81         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.81       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.61/0.81  thf('35', plain,
% 0.61/0.81      (![X7 : $i, X8 : $i]:
% 0.61/0.81         (~ (l1_pre_topc @ X7)
% 0.61/0.81          | ~ (v2_pre_topc @ X7)
% 0.61/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.61/0.81          | (v3_pre_topc @ (k1_tops_1 @ X7 @ X8) @ X7))),
% 0.61/0.81      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.61/0.81  thf('36', plain,
% 0.61/0.81      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.61/0.81        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.81        | ~ (l1_pre_topc @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.81  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('39', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.61/0.81      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.61/0.81  thf('40', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf(t44_tops_1, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( l1_pre_topc @ A ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.81           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.61/0.81  thf('41', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.61/0.81          | (r1_tarski @ (k1_tops_1 @ X10 @ X9) @ X9)
% 0.61/0.81          | ~ (l1_pre_topc @ X10))),
% 0.61/0.81      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.61/0.81  thf('42', plain,
% 0.61/0.81      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['40', '41'])).
% 0.61/0.81  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('44', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.61/0.81      inference('demod', [status(thm)], ['42', '43'])).
% 0.61/0.81  thf('45', plain,
% 0.61/0.81      (![X4 : $i, X6 : $i]:
% 0.61/0.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.61/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.81  thf('46', plain,
% 0.61/0.81      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.81  thf('47', plain,
% 0.61/0.81      (![X1 : $i, X3 : $i]:
% 0.61/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.81  thf('48', plain,
% 0.61/0.81      (![X22 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81          | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A)
% 0.61/0.81          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('49', plain,
% 0.61/0.81      ((![X22 : $i]:
% 0.61/0.81          (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A)))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('split', [status(esa)], ['48'])).
% 0.61/0.81  thf('50', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 0.61/0.81              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['47', '49'])).
% 0.61/0.81  thf('51', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.81         ((r2_hidden @ X15 @ X16) | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('52', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (sk_D_1 @ (sk_C @ X0 @ sk_B)))))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.61/0.81  thf('53', plain,
% 0.61/0.81      ((![X22 : $i]:
% 0.61/0.81          (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))) | 
% 0.61/0.81       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.61/0.81      inference('split', [status(esa)], ['48'])).
% 0.61/0.81  thf('54', plain,
% 0.61/0.81      ((![X22 : $i]:
% 0.61/0.81          (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sat_resolution*', [status(thm)],
% 0.61/0.81                ['3', '14', '17', '18', '31', '53'])).
% 0.61/0.81  thf('55', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))),
% 0.61/0.81      inference('simpl_trail', [status(thm)], ['52', '54'])).
% 0.61/0.81  thf('56', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 0.61/0.81              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['47', '49'])).
% 0.61/0.81  thf('57', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.81         ((r1_tarski @ X16 @ X17) | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('58', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['56', '57'])).
% 0.61/0.81  thf('59', plain,
% 0.61/0.81      ((![X22 : $i]:
% 0.61/0.81          (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sat_resolution*', [status(thm)],
% 0.61/0.81                ['3', '14', '17', '18', '31', '53'])).
% 0.61/0.81  thf('60', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B))),
% 0.61/0.81      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 0.61/0.81  thf('61', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 0.61/0.81              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['47', '49'])).
% 0.61/0.81  thf('62', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.81         ((v3_pre_topc @ X16 @ X18) | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('63', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (v3_pre_topc @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_A)))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['61', '62'])).
% 0.61/0.81  thf('64', plain,
% 0.61/0.81      ((![X22 : $i]:
% 0.61/0.81          (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sat_resolution*', [status(thm)],
% 0.61/0.81                ['3', '14', '17', '18', '31', '53'])).
% 0.61/0.81  thf('65', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (v3_pre_topc @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.61/0.81      inference('simpl_trail', [status(thm)], ['63', '64'])).
% 0.61/0.81  thf('66', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 0.61/0.81              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['47', '49'])).
% 0.61/0.81  thf('67', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.81         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.61/0.81          | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('68', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((r1_tarski @ sk_B @ X0)
% 0.61/0.81           | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 0.61/0.81              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.61/0.81         <= ((![X22 : $i]:
% 0.61/0.81                (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81                 | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['66', '67'])).
% 0.61/0.81  thf('69', plain,
% 0.61/0.81      ((![X22 : $i]:
% 0.61/0.81          (~ (r2_hidden @ X22 @ sk_B)
% 0.61/0.81           | (zip_tseitin_0 @ (sk_D_1 @ X22) @ X22 @ sk_B @ sk_A)))),
% 0.61/0.81      inference('sat_resolution*', [status(thm)],
% 0.61/0.81                ['3', '14', '17', '18', '31', '53'])).
% 0.61/0.81  thf('70', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 0.61/0.81             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.81      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.61/0.81  thf('71', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf(t54_tops_1, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.81       ( ![B:$i,C:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.81           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.61/0.81             ( ?[D:$i]:
% 0.61/0.81               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.61/0.81                 ( v3_pre_topc @ D @ A ) & 
% 0.61/0.81                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.61/0.81  thf('72', plain,
% 0.61/0.81      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.81          | ~ (r2_hidden @ X13 @ X14)
% 0.61/0.81          | ~ (r1_tarski @ X14 @ X11)
% 0.61/0.81          | ~ (v3_pre_topc @ X14 @ X12)
% 0.61/0.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.81          | (r2_hidden @ X13 @ (k1_tops_1 @ X12 @ X11))
% 0.61/0.81          | ~ (l1_pre_topc @ X12)
% 0.61/0.81          | ~ (v2_pre_topc @ X12))),
% 0.61/0.81      inference('cnf', [status(esa)], [t54_tops_1])).
% 0.61/0.81  thf('73', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (v2_pre_topc @ sk_A)
% 0.61/0.81          | ~ (l1_pre_topc @ sk_A)
% 0.61/0.81          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.81          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.61/0.81          | ~ (r1_tarski @ X1 @ sk_B)
% 0.61/0.81          | ~ (r2_hidden @ X0 @ X1))),
% 0.61/0.81      inference('sup-', [status(thm)], ['71', '72'])).
% 0.61/0.81  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.81  thf('76', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.81          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.61/0.81          | ~ (r1_tarski @ X1 @ sk_B)
% 0.61/0.81          | ~ (r2_hidden @ X0 @ X1))),
% 0.61/0.81      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.61/0.81  thf('77', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | ~ (r2_hidden @ X1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)))
% 0.61/0.81          | ~ (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.61/0.81          | ~ (v3_pre_topc @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_A)
% 0.61/0.81          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['70', '76'])).
% 0.61/0.81  thf('78', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81          | ~ (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.61/0.81          | ~ (r2_hidden @ X1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)))
% 0.61/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['65', '77'])).
% 0.61/0.81  thf('79', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)))
% 0.61/0.81          | ~ (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.61/0.81          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['78'])).
% 0.61/0.81  thf('80', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81          | ~ (r2_hidden @ X1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['60', '79'])).
% 0.61/0.81  thf('81', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)))
% 0.61/0.81          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['80'])).
% 0.61/0.81  thf('82', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (r1_tarski @ sk_B @ X0)
% 0.61/0.81          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['55', '81'])).
% 0.61/0.81  thf('83', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['82'])).
% 0.61/0.81  thf('84', plain,
% 0.61/0.81      (![X1 : $i, X3 : $i]:
% 0.61/0.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.81  thf('85', plain,
% 0.61/0.81      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.81        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['83', '84'])).
% 0.61/0.81  thf('86', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.61/0.82      inference('simplify', [status(thm)], ['85'])).
% 0.61/0.82  thf('87', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['46', '86'])).
% 0.61/0.82  thf('88', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.61/0.82      inference('demod', [status(thm)], ['39', '87'])).
% 0.61/0.82  thf('89', plain, ($false), inference('demod', [status(thm)], ['33', '88'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
