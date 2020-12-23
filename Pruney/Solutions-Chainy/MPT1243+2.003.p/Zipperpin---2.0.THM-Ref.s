%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5H6RVVaS2

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:10 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 592 expanded)
%              Number of leaves         :   25 ( 159 expanded)
%              Depth                    :   25
%              Number of atoms          : 1498 (8132 expanded)
%              Number of equality atoms :   26 (  50 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ! [X27: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
      | ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_D_1 )
   <= ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_B )
   <= ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
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
        | ~ ( r2_hidden @ X0 @ sk_D_1 ) )
   <= ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
   <= ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
   <= ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ! [X27: $i] :
        ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X27: $i] :
        ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ! [X27: $i] :
          ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X27: $i] :
        ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A )
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
    ! [X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 @ sk_B @ sk_A )
      | ( r2_hidden @ X25 @ sk_B )
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
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X20 @ X19 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X23 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
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
    ( ! [X27: $i] :
        ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X27: $i] :
        ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ! [X27: $i] :
          ~ ( zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A )
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

thf('35',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != X17 )
      | ( v3_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('36',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 )
        | ( ( k1_tops_1 @ X18 @ X17 )
         != X17 )
        | ( v3_pre_topc @ X17 @ X18 ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 )
        | ( ( k1_tops_1 @ X18 @ X17 )
         != X17 )
        | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != X17 )
      | ( v3_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('39',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ~ ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 )
        | ( ( k1_tops_1 @ X18 @ X17 )
         != X17 )
        | ( v3_pre_topc @ X17 @ X18 ) )
    | ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != X17 )
      | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != X17 )
      | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference(simpl_trail,[status(thm)],['36','44'])).

thf('46',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('64',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['62','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('67',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','63'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ( ( k1_tops_1 @ X15 @ X16 )
        = X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('72',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
        | ~ ( v3_pre_topc @ X16 @ X15 )
        | ( ( k1_tops_1 @ X15 @ X16 )
          = X16 ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
        | ~ ( v3_pre_topc @ X16 @ X15 )
        | ( ( k1_tops_1 @ X15 @ X16 )
          = X16 ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(split,[status(esa)],['71'])).

thf('75',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,(
    ~ ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( l1_pre_topc @ X15 )
        | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
        | ~ ( v3_pre_topc @ X16 @ X15 )
        | ( ( k1_tops_1 @ X15 @ X16 )
          = X16 ) )
    | ! [X17: $i,X18: $i] :
        ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( l1_pre_topc @ X18 )
        | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(split,[status(esa)],['71'])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ( ( k1_tops_1 @ X15 @ X16 )
        = X16 ) ) ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X15 )
      | ( ( k1_tops_1 @ X15 @ X16 )
        = X16 ) ) ),
    inference(simpl_trail,[status(thm)],['72','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_D @ ( sk_C @ X0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_D @ ( sk_C @ X0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v3_pre_topc @ X20 @ X22 )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','63'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_D @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['84','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('99',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B ) )
   <= ! [X26: $i] :
        ( ~ ( r2_hidden @ X26 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X26 ) @ X26 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','63'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('111',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','112'])).

thf('114',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['49','113'])).

thf('115',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['33','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5H6RVVaS2
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.01/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.20  % Solved by: fo/fo7.sh
% 1.01/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.20  % done 1638 iterations in 0.741s
% 1.01/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.20  % SZS output start Refutation
% 1.01/1.20  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.01/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.01/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.01/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.01/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.01/1.20  thf(sk_D_type, type, sk_D: $i > $i).
% 1.01/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.20  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.01/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.01/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.01/1.20  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.01/1.20  thf(t57_tops_1, conjecture,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ( v3_pre_topc @ B @ A ) <=>
% 1.01/1.20             ( ![C:$i]:
% 1.01/1.20               ( ( r2_hidden @ C @ B ) <=>
% 1.01/1.20                 ( ?[D:$i]:
% 1.01/1.20                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.01/1.20                     ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ B ) & 
% 1.01/1.20                     ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.01/1.20  thf(zf_stmt_1, axiom,
% 1.01/1.20    (![D:$i,C:$i,B:$i,A:$i]:
% 1.01/1.20     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 1.01/1.20       ( ( r2_hidden @ C @ D ) & ( r1_tarski @ D @ B ) & 
% 1.01/1.20         ( v3_pre_topc @ D @ A ) & 
% 1.01/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_2, conjecture,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ( v3_pre_topc @ B @ A ) <=>
% 1.01/1.20             ( ![C:$i]:
% 1.01/1.20               ( ( r2_hidden @ C @ B ) <=>
% 1.01/1.20                 ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_3, negated_conjecture,
% 1.01/1.20    (~( ![A:$i]:
% 1.01/1.20        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.20          ( ![B:$i]:
% 1.01/1.20            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20              ( ( v3_pre_topc @ B @ A ) <=>
% 1.01/1.20                ( ![C:$i]:
% 1.01/1.20                  ( ( r2_hidden @ C @ B ) <=>
% 1.01/1.20                    ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) )),
% 1.01/1.20    inference('cnf.neg', [status(esa)], [zf_stmt_2])).
% 1.01/1.20  thf('0', plain,
% 1.01/1.20      (![X27 : $i]:
% 1.01/1.20         (~ (r2_hidden @ sk_C_1 @ sk_B)
% 1.01/1.20          | ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A)
% 1.01/1.20          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('1', plain,
% 1.01/1.20      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('2', plain,
% 1.01/1.20      (((r2_hidden @ sk_C_1 @ sk_B)
% 1.01/1.20        | (zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.01/1.20        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('3', plain,
% 1.01/1.20      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 1.01/1.20       ((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.01/1.20      inference('split', [status(esa)], ['2'])).
% 1.01/1.20  thf('4', plain,
% 1.01/1.20      (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))
% 1.01/1.20         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['2'])).
% 1.01/1.20  thf('5', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.01/1.20         ((r2_hidden @ X19 @ X20) | ~ (zip_tseitin_0 @ X20 @ X19 @ X21 @ X22))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.20  thf('6', plain,
% 1.01/1.20      (((r2_hidden @ sk_C_1 @ sk_D_1))
% 1.01/1.20         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.20  thf('7', plain,
% 1.01/1.20      (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))
% 1.01/1.20         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['2'])).
% 1.01/1.20  thf('8', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.01/1.20         ((r1_tarski @ X20 @ X21) | ~ (zip_tseitin_0 @ X20 @ X19 @ X21 @ X22))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.20  thf('9', plain,
% 1.01/1.20      (((r1_tarski @ sk_D_1 @ sk_B))
% 1.01/1.20         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf(d3_tarski, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( r1_tarski @ A @ B ) <=>
% 1.01/1.20       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.01/1.20  thf('10', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X0 @ X1)
% 1.01/1.20          | (r2_hidden @ X0 @ X2)
% 1.01/1.20          | ~ (r1_tarski @ X1 @ X2))),
% 1.01/1.20      inference('cnf', [status(esa)], [d3_tarski])).
% 1.01/1.20  thf('11', plain,
% 1.01/1.20      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_D_1)))
% 1.01/1.20         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['9', '10'])).
% 1.01/1.20  thf('12', plain,
% 1.01/1.20      (((r2_hidden @ sk_C_1 @ sk_B))
% 1.01/1.20         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['6', '11'])).
% 1.01/1.20  thf('13', plain,
% 1.01/1.20      ((~ (r2_hidden @ sk_C_1 @ sk_B)) <= (~ ((r2_hidden @ sk_C_1 @ sk_B)))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('14', plain,
% 1.01/1.20      (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) | 
% 1.01/1.20       ((r2_hidden @ sk_C_1 @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['12', '13'])).
% 1.01/1.20  thf('15', plain,
% 1.01/1.20      (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))
% 1.01/1.20         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['2'])).
% 1.01/1.20  thf('16', plain,
% 1.01/1.20      ((![X27 : $i]: ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A))
% 1.01/1.20         <= ((![X27 : $i]: ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('17', plain,
% 1.01/1.20      (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) | 
% 1.01/1.20       ~ (![X27 : $i]: ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.01/1.20  thf('18', plain,
% 1.01/1.20      ((![X27 : $i]: ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A)) | 
% 1.01/1.20       ~ ((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('19', plain,
% 1.01/1.20      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 1.01/1.20      inference('split', [status(esa)], ['2'])).
% 1.01/1.20  thf(d10_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.01/1.20  thf('20', plain,
% 1.01/1.20      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.01/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.01/1.20  thf('21', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.01/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.01/1.20  thf('22', plain,
% 1.01/1.20      (![X24 : $i, X25 : $i]:
% 1.01/1.20         (~ (zip_tseitin_0 @ X24 @ X25 @ sk_B @ sk_A)
% 1.01/1.20          | (r2_hidden @ X25 @ sk_B)
% 1.01/1.20          | (v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('23', plain,
% 1.01/1.20      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['22'])).
% 1.01/1.20  thf('24', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('25', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.01/1.20         ((zip_tseitin_0 @ X20 @ X19 @ X21 @ X23)
% 1.01/1.20          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.01/1.20          | ~ (v3_pre_topc @ X20 @ X23)
% 1.01/1.20          | ~ (r1_tarski @ X20 @ X21)
% 1.01/1.20          | ~ (r2_hidden @ X19 @ X20))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.20  thf('26', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X0 @ sk_B)
% 1.01/1.20          | ~ (r1_tarski @ sk_B @ X1)
% 1.01/1.20          | ~ (v3_pre_topc @ sk_B @ sk_A)
% 1.01/1.20          | (zip_tseitin_0 @ sk_B @ X0 @ X1 @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['24', '25'])).
% 1.01/1.20  thf('27', plain,
% 1.01/1.20      ((![X0 : $i, X1 : $i]:
% 1.01/1.20          ((zip_tseitin_0 @ sk_B @ X1 @ X0 @ sk_A)
% 1.01/1.20           | ~ (r1_tarski @ sk_B @ X0)
% 1.01/1.20           | ~ (r2_hidden @ X1 @ sk_B)))
% 1.01/1.20         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['23', '26'])).
% 1.01/1.20  thf('28', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          (~ (r2_hidden @ X0 @ sk_B)
% 1.01/1.20           | (zip_tseitin_0 @ sk_B @ X0 @ sk_B @ sk_A)))
% 1.01/1.20         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['21', '27'])).
% 1.01/1.20  thf('29', plain,
% 1.01/1.20      (((zip_tseitin_0 @ sk_B @ sk_C_1 @ sk_B @ sk_A))
% 1.01/1.20         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['19', '28'])).
% 1.01/1.20  thf('30', plain,
% 1.01/1.20      ((![X27 : $i]: ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A))
% 1.01/1.20         <= ((![X27 : $i]: ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('split', [status(esa)], ['0'])).
% 1.01/1.20  thf('31', plain,
% 1.01/1.20      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 1.01/1.20       ~ (![X27 : $i]: ~ (zip_tseitin_0 @ X27 @ sk_C_1 @ sk_B @ sk_A)) | 
% 1.01/1.20       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['29', '30'])).
% 1.01/1.20  thf('32', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['3', '14', '17', '18', '31'])).
% 1.01/1.20  thf('33', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 1.01/1.20  thf('34', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf(t55_tops_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( l1_pre_topc @ B ) =>
% 1.01/1.20           ( ![C:$i]:
% 1.01/1.20             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20               ( ![D:$i]:
% 1.01/1.20                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.01/1.20                   ( ( ( v3_pre_topc @ D @ B ) =>
% 1.01/1.20                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 1.01/1.20                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 1.01/1.20                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf('35', plain,
% 1.01/1.20      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.01/1.20         (~ (l1_pre_topc @ X15)
% 1.01/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20          | ((k1_tops_1 @ X18 @ X17) != (X17))
% 1.01/1.20          | (v3_pre_topc @ X17 @ X18)
% 1.01/1.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20          | ~ (l1_pre_topc @ X18)
% 1.01/1.20          | ~ (v2_pre_topc @ X18))),
% 1.01/1.20      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.01/1.20  thf('36', plain,
% 1.01/1.20      ((![X17 : $i, X18 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20           | ~ (l1_pre_topc @ X18)
% 1.01/1.20           | ~ (v2_pre_topc @ X18)
% 1.01/1.20           | ((k1_tops_1 @ X18 @ X17) != (X17))
% 1.01/1.20           | (v3_pre_topc @ X17 @ X18)))
% 1.01/1.20         <= ((![X17 : $i, X18 : $i]:
% 1.01/1.20                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20                 | ~ (l1_pre_topc @ X18)
% 1.01/1.20                 | ~ (v2_pre_topc @ X18)
% 1.01/1.20                 | ((k1_tops_1 @ X18 @ X17) != (X17))
% 1.01/1.20                 | (v3_pre_topc @ X17 @ X18))))),
% 1.01/1.20      inference('split', [status(esa)], ['35'])).
% 1.01/1.20  thf('37', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('38', plain,
% 1.01/1.20      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.01/1.20         (~ (l1_pre_topc @ X15)
% 1.01/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20          | ((k1_tops_1 @ X18 @ X17) != (X17))
% 1.01/1.20          | (v3_pre_topc @ X17 @ X18)
% 1.01/1.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20          | ~ (l1_pre_topc @ X18)
% 1.01/1.20          | ~ (v2_pre_topc @ X18))),
% 1.01/1.20      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.01/1.20  thf('39', plain,
% 1.01/1.20      ((![X15 : $i, X16 : $i]:
% 1.01/1.20          (~ (l1_pre_topc @ X15)
% 1.01/1.20           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))))
% 1.01/1.20         <= ((![X15 : $i, X16 : $i]:
% 1.01/1.20                (~ (l1_pre_topc @ X15)
% 1.01/1.20                 | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))))),
% 1.01/1.20      inference('split', [status(esa)], ['38'])).
% 1.01/1.20  thf('40', plain,
% 1.01/1.20      ((~ (l1_pre_topc @ sk_A))
% 1.01/1.20         <= ((![X15 : $i, X16 : $i]:
% 1.01/1.20                (~ (l1_pre_topc @ X15)
% 1.01/1.20                 | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['37', '39'])).
% 1.01/1.20  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('42', plain,
% 1.01/1.20      (~
% 1.01/1.20       (![X15 : $i, X16 : $i]:
% 1.01/1.20          (~ (l1_pre_topc @ X15)
% 1.01/1.20           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['40', '41'])).
% 1.01/1.20  thf('43', plain,
% 1.01/1.20      ((![X17 : $i, X18 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20           | ~ (l1_pre_topc @ X18)
% 1.01/1.20           | ~ (v2_pre_topc @ X18)
% 1.01/1.20           | ((k1_tops_1 @ X18 @ X17) != (X17))
% 1.01/1.20           | (v3_pre_topc @ X17 @ X18))) | 
% 1.01/1.20       (![X15 : $i, X16 : $i]:
% 1.01/1.20          (~ (l1_pre_topc @ X15)
% 1.01/1.20           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))))),
% 1.01/1.20      inference('split', [status(esa)], ['38'])).
% 1.01/1.20  thf('44', plain,
% 1.01/1.20      ((![X17 : $i, X18 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20           | ~ (l1_pre_topc @ X18)
% 1.01/1.20           | ~ (v2_pre_topc @ X18)
% 1.01/1.20           | ((k1_tops_1 @ X18 @ X17) != (X17))
% 1.01/1.20           | (v3_pre_topc @ X17 @ X18)))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 1.01/1.20  thf('45', plain,
% 1.01/1.20      (![X17 : $i, X18 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20          | ~ (l1_pre_topc @ X18)
% 1.01/1.20          | ~ (v2_pre_topc @ X18)
% 1.01/1.20          | ((k1_tops_1 @ X18 @ X17) != (X17))
% 1.01/1.20          | (v3_pre_topc @ X17 @ X18))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['36', '44'])).
% 1.01/1.20  thf('46', plain,
% 1.01/1.20      (((v3_pre_topc @ sk_B @ sk_A)
% 1.01/1.20        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 1.01/1.20        | ~ (v2_pre_topc @ sk_A)
% 1.01/1.20        | ~ (l1_pre_topc @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['34', '45'])).
% 1.01/1.20  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('49', plain,
% 1.01/1.20      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 1.01/1.20      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.01/1.20  thf('50', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf(t44_tops_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( l1_pre_topc @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.01/1.20  thf('51', plain,
% 1.01/1.20      (![X10 : $i, X11 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ X10)
% 1.01/1.20          | ~ (l1_pre_topc @ X11))),
% 1.01/1.20      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.01/1.20  thf('52', plain,
% 1.01/1.20      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['50', '51'])).
% 1.01/1.20  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('54', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.01/1.20      inference('demod', [status(thm)], ['52', '53'])).
% 1.01/1.20  thf('55', plain,
% 1.01/1.20      (![X4 : $i, X6 : $i]:
% 1.01/1.20         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.01/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.01/1.20  thf('56', plain,
% 1.01/1.20      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.01/1.20        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['54', '55'])).
% 1.01/1.20  thf('57', plain,
% 1.01/1.20      (![X1 : $i, X3 : $i]:
% 1.01/1.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.01/1.20      inference('cnf', [status(esa)], [d3_tarski])).
% 1.01/1.20  thf('58', plain,
% 1.01/1.20      (![X26 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20          | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A)
% 1.01/1.20          | (v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('59', plain,
% 1.01/1.20      ((![X26 : $i]:
% 1.01/1.20          (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A)))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('split', [status(esa)], ['58'])).
% 1.01/1.20  thf('60', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ sk_B @ X0)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['57', '59'])).
% 1.01/1.20  thf('61', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.01/1.20         ((r2_hidden @ X19 @ X20) | ~ (zip_tseitin_0 @ X20 @ X19 @ X21 @ X22))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.20  thf('62', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ sk_B @ X0)
% 1.01/1.20           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (sk_D @ (sk_C @ X0 @ sk_B)))))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['60', '61'])).
% 1.01/1.20  thf('63', plain,
% 1.01/1.20      ((![X26 : $i]:
% 1.01/1.20          (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))) | 
% 1.01/1.20       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.01/1.20      inference('split', [status(esa)], ['58'])).
% 1.01/1.20  thf('64', plain,
% 1.01/1.20      ((![X26 : $i]:
% 1.01/1.20          (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)],
% 1.01/1.20                ['3', '14', '17', '18', '31', '63'])).
% 1.01/1.20  thf('65', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (sk_D @ (sk_C @ X0 @ sk_B))))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['62', '64'])).
% 1.01/1.20  thf('66', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ sk_B @ X0)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['57', '59'])).
% 1.01/1.20  thf('67', plain,
% 1.01/1.20      ((![X26 : $i]:
% 1.01/1.20          (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)],
% 1.01/1.20                ['3', '14', '17', '18', '31', '63'])).
% 1.01/1.20  thf('68', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20             (sk_C @ X0 @ sk_B) @ sk_B @ sk_A))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 1.01/1.20  thf('69', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.01/1.20         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.20          | ~ (zip_tseitin_0 @ X20 @ X19 @ X21 @ X22))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.20  thf('70', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['68', '69'])).
% 1.01/1.20  thf('71', plain,
% 1.01/1.20      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.01/1.20         (~ (l1_pre_topc @ X15)
% 1.01/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20          | ~ (v3_pre_topc @ X16 @ X15)
% 1.01/1.20          | ((k1_tops_1 @ X15 @ X16) = (X16))
% 1.01/1.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20          | ~ (l1_pre_topc @ X18)
% 1.01/1.20          | ~ (v2_pre_topc @ X18))),
% 1.01/1.20      inference('cnf', [status(esa)], [t55_tops_1])).
% 1.01/1.20  thf('72', plain,
% 1.01/1.20      ((![X15 : $i, X16 : $i]:
% 1.01/1.20          (~ (l1_pre_topc @ X15)
% 1.01/1.20           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20           | ~ (v3_pre_topc @ X16 @ X15)
% 1.01/1.20           | ((k1_tops_1 @ X15 @ X16) = (X16))))
% 1.01/1.20         <= ((![X15 : $i, X16 : $i]:
% 1.01/1.20                (~ (l1_pre_topc @ X15)
% 1.01/1.20                 | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20                 | ~ (v3_pre_topc @ X16 @ X15)
% 1.01/1.20                 | ((k1_tops_1 @ X15 @ X16) = (X16)))))),
% 1.01/1.20      inference('split', [status(esa)], ['71'])).
% 1.01/1.20  thf('73', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('74', plain,
% 1.01/1.20      ((![X17 : $i, X18 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20           | ~ (l1_pre_topc @ X18)
% 1.01/1.20           | ~ (v2_pre_topc @ X18)))
% 1.01/1.20         <= ((![X17 : $i, X18 : $i]:
% 1.01/1.20                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20                 | ~ (l1_pre_topc @ X18)
% 1.01/1.20                 | ~ (v2_pre_topc @ X18))))),
% 1.01/1.20      inference('split', [status(esa)], ['71'])).
% 1.01/1.20  thf('75', plain,
% 1.01/1.20      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 1.01/1.20         <= ((![X17 : $i, X18 : $i]:
% 1.01/1.20                (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20                 | ~ (l1_pre_topc @ X18)
% 1.01/1.20                 | ~ (v2_pre_topc @ X18))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['73', '74'])).
% 1.01/1.20  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('78', plain,
% 1.01/1.20      (~
% 1.01/1.20       (![X17 : $i, X18 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20           | ~ (l1_pre_topc @ X18)
% 1.01/1.20           | ~ (v2_pre_topc @ X18)))),
% 1.01/1.20      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.01/1.20  thf('79', plain,
% 1.01/1.20      ((![X15 : $i, X16 : $i]:
% 1.01/1.20          (~ (l1_pre_topc @ X15)
% 1.01/1.20           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20           | ~ (v3_pre_topc @ X16 @ X15)
% 1.01/1.20           | ((k1_tops_1 @ X15 @ X16) = (X16)))) | 
% 1.01/1.20       (![X17 : $i, X18 : $i]:
% 1.01/1.20          (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.01/1.20           | ~ (l1_pre_topc @ X18)
% 1.01/1.20           | ~ (v2_pre_topc @ X18)))),
% 1.01/1.20      inference('split', [status(esa)], ['71'])).
% 1.01/1.20  thf('80', plain,
% 1.01/1.20      ((![X15 : $i, X16 : $i]:
% 1.01/1.20          (~ (l1_pre_topc @ X15)
% 1.01/1.20           | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20           | ~ (v3_pre_topc @ X16 @ X15)
% 1.01/1.20           | ((k1_tops_1 @ X15 @ X16) = (X16))))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 1.01/1.20  thf('81', plain,
% 1.01/1.20      (![X15 : $i, X16 : $i]:
% 1.01/1.20         (~ (l1_pre_topc @ X15)
% 1.01/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.20          | ~ (v3_pre_topc @ X16 @ X15)
% 1.01/1.20          | ((k1_tops_1 @ X15 @ X16) = (X16)))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['72', '80'])).
% 1.01/1.20  thf('82', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | ((k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B)))
% 1.01/1.20              = (sk_D @ (sk_C @ X0 @ sk_B)))
% 1.01/1.20          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A)
% 1.01/1.20          | ~ (l1_pre_topc @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['70', '81'])).
% 1.01/1.20  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('84', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | ((k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B)))
% 1.01/1.20              = (sk_D @ (sk_C @ X0 @ sk_B)))
% 1.01/1.20          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['82', '83'])).
% 1.01/1.20  thf('85', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ sk_B @ X0)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['57', '59'])).
% 1.01/1.20  thf('86', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.01/1.20         ((v3_pre_topc @ X20 @ X22) | ~ (zip_tseitin_0 @ X20 @ X19 @ X21 @ X22))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.20  thf('87', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ sk_B @ X0)
% 1.01/1.20           | (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A)))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['85', '86'])).
% 1.01/1.20  thf('88', plain,
% 1.01/1.20      ((![X26 : $i]:
% 1.01/1.20          (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)],
% 1.01/1.20                ['3', '14', '17', '18', '31', '63'])).
% 1.01/1.20  thf('89', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('90', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (((k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B)))
% 1.01/1.20            = (sk_D @ (sk_C @ X0 @ sk_B)))
% 1.01/1.20          | (r1_tarski @ sk_B @ X0))),
% 1.01/1.20      inference('clc', [status(thm)], ['84', '89'])).
% 1.01/1.20  thf('91', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('92', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['68', '69'])).
% 1.01/1.20  thf(t48_tops_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( l1_pre_topc @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20           ( ![C:$i]:
% 1.01/1.20             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.20               ( ( r1_tarski @ B @ C ) =>
% 1.01/1.20                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf('93', plain,
% 1.01/1.20      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.01/1.20          | ~ (r1_tarski @ X12 @ X14)
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ (k1_tops_1 @ X13 @ X14))
% 1.01/1.20          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.01/1.20          | ~ (l1_pre_topc @ X13))),
% 1.01/1.20      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.01/1.20  thf('94', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 1.01/1.20             (k1_tops_1 @ sk_A @ X1))
% 1.01/1.20          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1))),
% 1.01/1.20      inference('sup-', [status(thm)], ['92', '93'])).
% 1.01/1.20  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.20  thf('96', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 1.01/1.20             (k1_tops_1 @ sk_A @ X1))
% 1.01/1.20          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1))),
% 1.01/1.20      inference('demod', [status(thm)], ['94', '95'])).
% 1.01/1.20  thf('97', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 1.01/1.20             (k1_tops_1 @ sk_A @ sk_B))
% 1.01/1.20          | (r1_tarski @ sk_B @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['91', '96'])).
% 1.01/1.20  thf('98', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ sk_B @ X0)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['57', '59'])).
% 1.01/1.20  thf('99', plain,
% 1.01/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.01/1.20         ((r1_tarski @ X20 @ X21) | ~ (zip_tseitin_0 @ X20 @ X19 @ X21 @ X22))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.20  thf('100', plain,
% 1.01/1.20      ((![X0 : $i]:
% 1.01/1.20          ((r1_tarski @ sk_B @ X0)
% 1.01/1.20           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)))
% 1.01/1.20         <= ((![X26 : $i]:
% 1.01/1.20                (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20                 | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['98', '99'])).
% 1.01/1.20  thf('101', plain,
% 1.01/1.20      ((![X26 : $i]:
% 1.01/1.20          (~ (r2_hidden @ X26 @ sk_B)
% 1.01/1.20           | (zip_tseitin_0 @ (sk_D @ X26) @ X26 @ sk_B @ sk_A)))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)],
% 1.01/1.20                ['3', '14', '17', '18', '31', '63'])).
% 1.01/1.20  thf('102', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['100', '101'])).
% 1.01/1.20  thf('103', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 1.01/1.20             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('clc', [status(thm)], ['97', '102'])).
% 1.01/1.20  thf('104', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.01/1.20          | (r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (r1_tarski @ sk_B @ X0))),
% 1.01/1.20      inference('sup+', [status(thm)], ['90', '103'])).
% 1.01/1.20  thf('105', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 1.01/1.20             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('simplify', [status(thm)], ['104'])).
% 1.01/1.20  thf('106', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X0 @ X1)
% 1.01/1.20          | (r2_hidden @ X0 @ X2)
% 1.01/1.20          | ~ (r1_tarski @ X1 @ X2))),
% 1.01/1.20      inference('cnf', [status(esa)], [d3_tarski])).
% 1.01/1.20  thf('107', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 1.01/1.20          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C @ X0 @ sk_B))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['105', '106'])).
% 1.01/1.20  thf('108', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r1_tarski @ sk_B @ X0)
% 1.01/1.20          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.01/1.20          | (r1_tarski @ sk_B @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['65', '107'])).
% 1.01/1.20  thf('109', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.01/1.20          | (r1_tarski @ sk_B @ X0))),
% 1.01/1.20      inference('simplify', [status(thm)], ['108'])).
% 1.01/1.20  thf('110', plain,
% 1.01/1.20      (![X1 : $i, X3 : $i]:
% 1.01/1.20         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.01/1.20      inference('cnf', [status(esa)], [d3_tarski])).
% 1.01/1.20  thf('111', plain,
% 1.01/1.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.01/1.20        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['109', '110'])).
% 1.01/1.20  thf('112', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 1.01/1.20      inference('simplify', [status(thm)], ['111'])).
% 1.01/1.20  thf('113', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 1.01/1.20      inference('demod', [status(thm)], ['56', '112'])).
% 1.01/1.20  thf('114', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 1.01/1.20      inference('demod', [status(thm)], ['49', '113'])).
% 1.01/1.20  thf('115', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 1.01/1.20      inference('simplify', [status(thm)], ['114'])).
% 1.01/1.20  thf('116', plain, ($false), inference('demod', [status(thm)], ['33', '115'])).
% 1.01/1.20  
% 1.01/1.20  % SZS output end Refutation
% 1.01/1.20  
% 1.04/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
