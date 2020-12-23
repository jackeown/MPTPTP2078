%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NOjFMo631c

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 695 expanded)
%              Number of leaves         :   27 ( 197 expanded)
%              Depth                    :   19
%              Number of atoms          : 1272 (12403 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t8_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( m1_connsp_2 @ C @ A @ B )
                <=> ? [D: $i] :
                      ( ( r2_hidden @ B @ D )
                      & ( r1_tarski @ D @ C )
                      & ( v3_pre_topc @ D @ A )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
   <= ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D_2 @ X0 )
        | ~ ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_tops_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D_2 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_2 @ X0 )
        | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D_2 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_2 @ X0 )
        | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D_2 @ X0 )
        | ( r1_tarski @ sk_D_2 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,
    ( ( ( r1_tarski @ sk_D_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_D_2 @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('23',plain,
    ( ( r1_tarski @ sk_D_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
   <= ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t57_tops_1,axiom,(
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

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ D )
        & ( r1_tarski @ D @ B )
        & ( v3_pre_topc @ D @ A )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X17 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D_2 )
        | ~ ( r1_tarski @ sk_D_2 @ X1 )
        | ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
        | ( zip_tseitin_0 @ sk_D_2 @ X0 @ X1 @ sk_A ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_2 @ X1 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_D_2 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_D_2 ) )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D_2 )
        | ( zip_tseitin_0 @ sk_D_2 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( zip_tseitin_0 @ sk_D_2 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
   <= ( ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','29'])).

thf('31',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X9 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
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

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( zip_tseitin_0 @ X21 @ X20 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('48',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('55',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('56',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('69',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( r1_tarski @ X30 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X30 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X30 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('73',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
   <= ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('77',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('79',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X30 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference(split,[status(esa)],['69'])).

thf('80',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      | ~ ( r1_tarski @ sk_D_2 @ sk_C_1 )
      | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X30 ) )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('82',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D_2 )
      | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X30 ) )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X30 ) )
      & ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X30 ) )
    | ~ ( r1_tarski @ sk_D_2 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_D_2 )
    | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X30 ) ) ),
    inference(split,[status(esa)],['69'])).

thf('86',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('87',plain,(
    r2_hidden @ sk_B @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['54','55','75','84','85','86'])).

thf('88',plain,(
    r1_tarski @ sk_D_2 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['86','55','75','84','85','54'])).

thf('89',plain,(
    v3_pre_topc @ sk_D_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['86','54','75','84','85','55'])).

thf('90',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['53','87','88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['69'])).

thf('101',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['86','54','55','75','84','85'])).

thf('102',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['99','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NOjFMo631c
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 379 iterations in 0.085s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(t8_connsp_2, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.54                 ( ?[D:$i]:
% 0.20/0.54                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.54                     ( v3_pre_topc @ D @ A ) & 
% 0.20/0.54                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54            ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.54                    ( ?[D:$i]:
% 0.20/0.54                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.54                        ( v3_pre_topc @ D @ A ) & 
% 0.20/0.54                        ( m1_subset_1 @
% 0.20/0.54                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.20/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_D_2) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_D_2)) <= (((r2_hidden @ sk_B @ sk_D_2)))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D_2 @ sk_A) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D_2 @ sk_A)) <= (((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t3_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('8', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (((r1_tarski @ sk_D_2 @ sk_C_1) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (((r1_tarski @ sk_D_2 @ sk_C_1)) <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['9'])).
% 0.20/0.54  thf(t1_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.54       ( r1_tarski @ A @ C ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.54          | (r1_tarski @ X0 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      ((![X0 : $i]: ((r1_tarski @ sk_D_2 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (((r1_tarski @ sk_D_2 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf(t56_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.54                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.54          | ~ (v3_pre_topc @ X10 @ X11)
% 0.20/0.54          | ~ (r1_tarski @ X10 @ X12)
% 0.20/0.54          | (r1_tarski @ X10 @ (k1_tops_1 @ X11 @ X12))
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.54          | ~ (l1_pre_topc @ X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (l1_pre_topc @ sk_A)
% 0.20/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | (r1_tarski @ sk_D_2 @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.54           | ~ (r1_tarski @ sk_D_2 @ X0)
% 0.20/0.54           | ~ (v3_pre_topc @ sk_D_2 @ sk_A)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | (r1_tarski @ sk_D_2 @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.54           | ~ (r1_tarski @ sk_D_2 @ X0)
% 0.20/0.54           | ~ (v3_pre_topc @ sk_D_2 @ sk_A)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (r1_tarski @ sk_D_2 @ X0)
% 0.20/0.54           | (r1_tarski @ sk_D_2 @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((((r1_tarski @ sk_D_2 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54         | ~ (r1_tarski @ sk_D_2 @ sk_C_1)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((r1_tarski @ sk_D_2 @ sk_C_1)) <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['9'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (((r1_tarski @ sk_D_2 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D_2 @ sk_A)) <= (((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf(t57_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.54             ( ![C:$i]:
% 0.20/0.54               ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.54                 ( ?[D:$i]:
% 0.20/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.54                     ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ B ) & 
% 0.20/0.54                     ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, axiom,
% 0.20/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.54       ( ( r2_hidden @ C @ D ) & ( r1_tarski @ D @ B ) & 
% 0.20/0.54         ( v3_pre_topc @ D @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X14 @ X13 @ X15 @ X17)
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.54          | ~ (v3_pre_topc @ X14 @ X17)
% 0.20/0.54          | ~ (r1_tarski @ X14 @ X15)
% 0.20/0.54          | ~ (r2_hidden @ X13 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((![X0 : $i, X1 : $i]:
% 0.20/0.54          (~ (r2_hidden @ X0 @ sk_D_2)
% 0.20/0.54           | ~ (r1_tarski @ sk_D_2 @ X1)
% 0.20/0.54           | ~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 0.20/0.54           | (zip_tseitin_0 @ sk_D_2 @ X0 @ X1 @ sk_A)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((![X0 : $i, X1 : $i]:
% 0.20/0.54          ((zip_tseitin_0 @ sk_D_2 @ X1 @ X0 @ sk_A)
% 0.20/0.54           | ~ (r1_tarski @ sk_D_2 @ X0)
% 0.20/0.54           | ~ (r2_hidden @ X1 @ sk_D_2)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (r2_hidden @ X0 @ sk_D_2)
% 0.20/0.54           | (zip_tseitin_0 @ sk_D_2 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (((zip_tseitin_0 @ sk_D_2 @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))
% 0.20/0.54         <= (((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.54             ((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.20/0.54             ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '29'])).
% 0.20/0.54  thf('31', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t44_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.54          | (r1_tarski @ (k1_tops_1 @ X9 @ X8) @ X8)
% 0.20/0.54          | ~ (l1_pre_topc @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('36', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.54          | (r1_tarski @ X0 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.20/0.54          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_3, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.54             ( ![C:$i]:
% 0.20/0.54               ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.54                 ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.54          | ~ (v3_pre_topc @ X18 @ X19)
% 0.20/0.54          | (r2_hidden @ X20 @ X18)
% 0.20/0.54          | ~ (zip_tseitin_0 @ X21 @ X20 @ X18 @ X19)
% 0.20/0.54          | ~ (l1_pre_topc @ X19)
% 0.20/0.54          | ~ (v2_pre_topc @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.20/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(fc9_tops_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X6)
% 0.20/0.54          | ~ (v2_pre_topc @ X6)
% 0.20/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.54          | (v3_pre_topc @ (k1_tops_1 @ X6 @ X7) @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.54  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('51', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (zip_tseitin_0 @ X1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.20/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '44', '45', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.54         <= (((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.54             ((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.20/0.54             ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['30', '52'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (((r1_tarski @ sk_D_2 @ sk_C_1)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['9'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D_2 @ sk_A)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.54         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d1_connsp_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.54                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.20/0.54          | ~ (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.20/0.54          | (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.54          | ~ (l1_pre_topc @ X25)
% 0.20/0.54          | ~ (v2_pre_topc @ X25)
% 0.20/0.54          | (v2_struct_0 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_A)
% 0.20/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.54         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['56', '62'])).
% 0.20/0.54  thf('64', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.54  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.54         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (![X30 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54          | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54          | ~ (r2_hidden @ sk_B @ X30)
% 0.20/0.54          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      ((![X30 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54           | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54           | ~ (r2_hidden @ sk_B @ X30)))
% 0.20/0.54         <= ((![X30 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54                 | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.20/0.54      inference('split', [status(esa)], ['69'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.20/0.54         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.20/0.54         <= ((![X30 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54                 | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.54  thf('72', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('73', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.54         <= ((![X30 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54                 | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.20/0.54      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.20/0.54       ~
% 0.20/0.54       (![X30 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54           | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54           | ~ (r2_hidden @ sk_B @ X30)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['67', '74'])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D_2 @ sk_A)) <= (((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_D_2)) <= (((r2_hidden @ sk_B @ sk_D_2)))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      ((![X30 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54           | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54           | ~ (r2_hidden @ sk_B @ X30)))
% 0.20/0.54         <= ((![X30 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54                 | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54                 | ~ (r2_hidden @ sk_B @ X30))))),
% 0.20/0.54      inference('split', [status(esa)], ['69'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      (((~ (r2_hidden @ sk_B @ sk_D_2)
% 0.20/0.54         | ~ (r1_tarski @ sk_D_2 @ sk_C_1)
% 0.20/0.54         | ~ (v3_pre_topc @ sk_D_2 @ sk_A)))
% 0.20/0.54         <= ((![X30 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54                 | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54                 | ~ (r2_hidden @ sk_B @ X30))) & 
% 0.20/0.54             ((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      (((r1_tarski @ sk_D_2 @ sk_C_1)) <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['9'])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (((~ (r2_hidden @ sk_B @ sk_D_2) | ~ (v3_pre_topc @ sk_D_2 @ sk_A)))
% 0.20/0.54         <= ((![X30 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54                 | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54                 | ~ (r2_hidden @ sk_B @ X30))) & 
% 0.20/0.54             ((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      ((~ (v3_pre_topc @ sk_D_2 @ sk_A))
% 0.20/0.54         <= ((![X30 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54                 | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54                 | ~ (r2_hidden @ sk_B @ X30))) & 
% 0.20/0.54             ((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.20/0.54             ((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['77', '82'])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      (~
% 0.20/0.54       (![X30 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54           | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54           | ~ (r2_hidden @ sk_B @ X30))) | 
% 0.20/0.54       ~ ((r1_tarski @ sk_D_2 @ sk_C_1)) | ~ ((r2_hidden @ sk_B @ sk_D_2)) | 
% 0.20/0.54       ~ ((v3_pre_topc @ sk_D_2 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['76', '83'])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.20/0.54       (![X30 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.20/0.54           | ~ (r1_tarski @ X30 @ sk_C_1)
% 0.20/0.54           | ~ (r2_hidden @ sk_B @ X30)))),
% 0.20/0.54      inference('split', [status(esa)], ['69'])).
% 0.20/0.54  thf('86', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_D_2)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('split', [status(esa)], ['1'])).
% 0.20/0.54  thf('87', plain, (((r2_hidden @ sk_B @ sk_D_2))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)],
% 0.20/0.54                ['54', '55', '75', '84', '85', '86'])).
% 0.20/0.54  thf('88', plain, (((r1_tarski @ sk_D_2 @ sk_C_1))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)],
% 0.20/0.54                ['86', '55', '75', '84', '85', '54'])).
% 0.20/0.54  thf('89', plain, (((v3_pre_topc @ sk_D_2 @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)],
% 0.20/0.54                ['86', '54', '75', '84', '85', '55'])).
% 0.20/0.54  thf('90', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['53', '87', '88', '89'])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('92', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.20/0.54          | ~ (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.20/0.54          | (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.54          | ~ (l1_pre_topc @ X25)
% 0.20/0.54          | ~ (v2_pre_topc @ X25)
% 0.20/0.54          | (v2_struct_0 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.54  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_A)
% 0.20/0.54          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['90', '96'])).
% 0.20/0.54  thf('98', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.54         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['69'])).
% 0.20/0.54  thf('101', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)],
% 0.20/0.54                ['86', '54', '55', '75', '84', '85'])).
% 0.20/0.54  thf('102', plain, (~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['100', '101'])).
% 0.20/0.54  thf('103', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('clc', [status(thm)], ['99', '102'])).
% 0.20/0.54  thf('104', plain, ($false), inference('demod', [status(thm)], ['0', '103'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
