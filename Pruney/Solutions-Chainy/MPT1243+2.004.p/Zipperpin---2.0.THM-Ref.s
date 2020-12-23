%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iuMQpKGKwt

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:10 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 483 expanded)
%              Number of leaves         :   25 ( 132 expanded)
%              Depth                    :   22
%              Number of atoms          : 1318 (6561 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X24: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
      | ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A )
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 ) ) ),
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
    ( ! [X24: $i] :
        ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X24: $i] :
        ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ~ ( zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ! [X24: $i] :
          ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X24: $i] :
        ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A )
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
    ! [X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 @ sk_B @ sk_A )
      | ( r2_hidden @ X22 @ sk_B )
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
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X20 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
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
    ( ! [X24: $i] :
        ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A )
   <= ! [X24: $i] :
        ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ! [X24: $i] :
          ~ ( zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A )
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
       != X11 )
      | ( v3_pre_topc @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('36',plain,
    ( ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 )
        | ( ( k1_tops_1 @ X12 @ X11 )
         != X11 )
        | ( v3_pre_topc @ X11 @ X12 ) )
   <= ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 )
        | ( ( k1_tops_1 @ X12 @ X11 )
         != X11 )
        | ( v3_pre_topc @ X11 @ X12 ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,
    ( ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
   <= ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(split,[status(esa)],['35'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ~ ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X11: $i,X12: $i] :
        ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
        | ~ ( l1_pre_topc @ X12 )
        | ~ ( v2_pre_topc @ X12 )
        | ( ( k1_tops_1 @ X12 @ X11 )
         != X11 )
        | ( v3_pre_topc @ X11 @ X12 ) )
    | ! [X9: $i,X10: $i] :
        ( ~ ( l1_pre_topc @ X9 )
        | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(split,[status(esa)],['35'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( ( k1_tops_1 @ X12 @ X11 )
       != X11 )
      | ( v3_pre_topc @ X11 @ X12 ) ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( ( k1_tops_1 @ X12 @ X11 )
       != X11 )
      | ( v3_pre_topc @ X11 @ X12 ) ) ),
    inference(simpl_trail,[status(thm)],['36','43'])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('63',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('67',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v3_pre_topc @ X17 @ X19 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','62'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

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

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
        | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('77',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
        | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','62'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('84',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ sk_B )
        | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ X23 ) @ X23 @ sk_B @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','14','17','18','31','62'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['55','95'])).

thf('97',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['48','96'])).

thf('98',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['33','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iuMQpKGKwt
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 450 iterations in 0.213s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.50/0.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.50/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(sk_D_type, type, sk_D: $i > $i).
% 0.50/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.50/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.69  thf(t57_tops_1, conjecture,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69           ( ( v3_pre_topc @ B @ A ) <=>
% 0.50/0.69             ( ![C:$i]:
% 0.50/0.69               ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.69                 ( ?[D:$i]:
% 0.50/0.69                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.50/0.69                     ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ B ) & 
% 0.50/0.69                     ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.50/0.69  thf(zf_stmt_1, axiom,
% 0.50/0.69    (![D:$i,C:$i,B:$i,A:$i]:
% 0.50/0.69     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.50/0.69       ( ( r2_hidden @ C @ D ) & ( r1_tarski @ D @ B ) & 
% 0.50/0.69         ( v3_pre_topc @ D @ A ) & 
% 0.50/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_2, conjecture,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69           ( ( v3_pre_topc @ B @ A ) <=>
% 0.50/0.69             ( ![C:$i]:
% 0.50/0.69               ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.69                 ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_3, negated_conjecture,
% 0.50/0.69    (~( ![A:$i]:
% 0.50/0.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.69          ( ![B:$i]:
% 0.50/0.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69              ( ( v3_pre_topc @ B @ A ) <=>
% 0.50/0.69                ( ![C:$i]:
% 0.50/0.69                  ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.69                    ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [zf_stmt_2])).
% 0.50/0.69  thf('0', plain,
% 0.50/0.69      (![X24 : $i]:
% 0.50/0.69         (~ (r2_hidden @ sk_C_1 @ sk_B)
% 0.50/0.69          | ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A)
% 0.50/0.69          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('1', plain,
% 0.50/0.69      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('2', plain,
% 0.50/0.69      (((r2_hidden @ sk_C_1 @ sk_B)
% 0.50/0.69        | (zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.50/0.69        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 0.50/0.69       ((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.50/0.69      inference('split', [status(esa)], ['2'])).
% 0.50/0.69  thf('4', plain,
% 0.50/0.69      (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))
% 0.50/0.69         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['2'])).
% 0.50/0.69  thf('5', plain,
% 0.50/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.69         ((r2_hidden @ X16 @ X17) | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('6', plain,
% 0.50/0.69      (((r2_hidden @ sk_C_1 @ sk_D_1))
% 0.50/0.69         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))
% 0.50/0.69         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['2'])).
% 0.50/0.69  thf('8', plain,
% 0.50/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.69         ((r1_tarski @ X17 @ X18) | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('9', plain,
% 0.50/0.69      (((r1_tarski @ sk_D_1 @ sk_B))
% 0.50/0.69         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.50/0.69  thf(d3_tarski, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.69  thf('10', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.69          | (r2_hidden @ X0 @ X2)
% 0.50/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.69  thf('11', plain,
% 0.50/0.69      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_D_1)))
% 0.50/0.69         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      (((r2_hidden @ sk_C_1 @ sk_B))
% 0.50/0.69         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['6', '11'])).
% 0.50/0.69  thf('13', plain,
% 0.50/0.69      ((~ (r2_hidden @ sk_C_1 @ sk_B)) <= (~ ((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('14', plain,
% 0.50/0.69      (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.50/0.69       ((r2_hidden @ sk_C_1 @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.69  thf('15', plain,
% 0.50/0.69      (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A))
% 0.50/0.69         <= (((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['2'])).
% 0.50/0.69  thf('16', plain,
% 0.50/0.69      ((![X24 : $i]: ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A))
% 0.50/0.69         <= ((![X24 : $i]: ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('17', plain,
% 0.50/0.69      (~ ((zip_tseitin_0 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.50/0.69       ~ (![X24 : $i]: ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.69  thf('18', plain,
% 0.50/0.69      ((![X24 : $i]: ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.50/0.69       ~ ((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('19', plain,
% 0.50/0.69      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.50/0.69      inference('split', [status(esa)], ['2'])).
% 0.50/0.69  thf(d10_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.69  thf('20', plain,
% 0.50/0.69      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.69  thf('21', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.50/0.69      inference('simplify', [status(thm)], ['20'])).
% 0.50/0.69  thf('22', plain,
% 0.50/0.69      (![X21 : $i, X22 : $i]:
% 0.50/0.69         (~ (zip_tseitin_0 @ X21 @ X22 @ sk_B @ sk_A)
% 0.50/0.69          | (r2_hidden @ X22 @ sk_B)
% 0.50/0.69          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('23', plain,
% 0.50/0.69      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['22'])).
% 0.50/0.69  thf('24', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('25', plain,
% 0.50/0.69      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.50/0.69         ((zip_tseitin_0 @ X17 @ X16 @ X18 @ X20)
% 0.50/0.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.50/0.69          | ~ (v3_pre_topc @ X17 @ X20)
% 0.50/0.69          | ~ (r1_tarski @ X17 @ X18)
% 0.50/0.69          | ~ (r2_hidden @ X16 @ X17))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('26', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ sk_B)
% 0.50/0.69          | ~ (r1_tarski @ sk_B @ X1)
% 0.50/0.69          | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.50/0.69          | (zip_tseitin_0 @ sk_B @ X0 @ X1 @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.69  thf('27', plain,
% 0.50/0.69      ((![X0 : $i, X1 : $i]:
% 0.50/0.69          ((zip_tseitin_0 @ sk_B @ X1 @ X0 @ sk_A)
% 0.50/0.69           | ~ (r1_tarski @ sk_B @ X0)
% 0.50/0.69           | ~ (r2_hidden @ X1 @ sk_B)))
% 0.50/0.69         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['23', '26'])).
% 0.50/0.69  thf('28', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          (~ (r2_hidden @ X0 @ sk_B)
% 0.50/0.69           | (zip_tseitin_0 @ sk_B @ X0 @ sk_B @ sk_A)))
% 0.50/0.69         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['21', '27'])).
% 0.50/0.69  thf('29', plain,
% 0.50/0.69      (((zip_tseitin_0 @ sk_B @ sk_C_1 @ sk_B @ sk_A))
% 0.50/0.69         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['19', '28'])).
% 0.50/0.69  thf('30', plain,
% 0.50/0.69      ((![X24 : $i]: ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A))
% 0.50/0.69         <= ((![X24 : $i]: ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('31', plain,
% 0.50/0.69      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 0.50/0.69       ~ (![X24 : $i]: ~ (zip_tseitin_0 @ X24 @ sk_C_1 @ sk_B @ sk_A)) | 
% 0.50/0.69       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.69  thf('32', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)], ['3', '14', '17', '18', '31'])).
% 0.50/0.69  thf('33', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.50/0.69  thf('34', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf(t55_tops_1, axiom,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( l1_pre_topc @ B ) =>
% 0.50/0.69           ( ![C:$i]:
% 0.50/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69               ( ![D:$i]:
% 0.50/0.69                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.50/0.69                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.50/0.69                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.50/0.69                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.50/0.69                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.69  thf('35', plain,
% 0.50/0.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.50/0.69         (~ (l1_pre_topc @ X9)
% 0.50/0.69          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.50/0.69          | ((k1_tops_1 @ X12 @ X11) != (X11))
% 0.50/0.69          | (v3_pre_topc @ X11 @ X12)
% 0.50/0.69          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.69          | ~ (l1_pre_topc @ X12)
% 0.50/0.69          | ~ (v2_pre_topc @ X12))),
% 0.50/0.69      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.50/0.69  thf('36', plain,
% 0.50/0.69      ((![X11 : $i, X12 : $i]:
% 0.50/0.69          (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.69           | ~ (l1_pre_topc @ X12)
% 0.50/0.69           | ~ (v2_pre_topc @ X12)
% 0.50/0.69           | ((k1_tops_1 @ X12 @ X11) != (X11))
% 0.50/0.69           | (v3_pre_topc @ X11 @ X12)))
% 0.50/0.69         <= ((![X11 : $i, X12 : $i]:
% 0.50/0.69                (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.69                 | ~ (l1_pre_topc @ X12)
% 0.50/0.69                 | ~ (v2_pre_topc @ X12)
% 0.50/0.69                 | ((k1_tops_1 @ X12 @ X11) != (X11))
% 0.50/0.69                 | (v3_pre_topc @ X11 @ X12))))),
% 0.50/0.69      inference('split', [status(esa)], ['35'])).
% 0.50/0.69  thf('37', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('38', plain,
% 0.50/0.69      ((![X9 : $i, X10 : $i]:
% 0.50/0.69          (~ (l1_pre_topc @ X9)
% 0.50/0.69           | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))))
% 0.50/0.69         <= ((![X9 : $i, X10 : $i]:
% 0.50/0.69                (~ (l1_pre_topc @ X9)
% 0.50/0.69                 | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))))),
% 0.50/0.69      inference('split', [status(esa)], ['35'])).
% 0.50/0.69  thf('39', plain,
% 0.50/0.69      ((~ (l1_pre_topc @ sk_A))
% 0.50/0.69         <= ((![X9 : $i, X10 : $i]:
% 0.50/0.69                (~ (l1_pre_topc @ X9)
% 0.50/0.69                 | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.69  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('41', plain,
% 0.50/0.69      (~
% 0.50/0.69       (![X9 : $i, X10 : $i]:
% 0.50/0.69          (~ (l1_pre_topc @ X9)
% 0.50/0.69           | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))))),
% 0.50/0.69      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.69  thf('42', plain,
% 0.50/0.69      ((![X11 : $i, X12 : $i]:
% 0.50/0.69          (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.69           | ~ (l1_pre_topc @ X12)
% 0.50/0.69           | ~ (v2_pre_topc @ X12)
% 0.50/0.69           | ((k1_tops_1 @ X12 @ X11) != (X11))
% 0.50/0.69           | (v3_pre_topc @ X11 @ X12))) | 
% 0.50/0.69       (![X9 : $i, X10 : $i]:
% 0.50/0.69          (~ (l1_pre_topc @ X9)
% 0.50/0.69           | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))))),
% 0.50/0.69      inference('split', [status(esa)], ['35'])).
% 0.50/0.69  thf('43', plain,
% 0.50/0.69      ((![X11 : $i, X12 : $i]:
% 0.50/0.69          (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.69           | ~ (l1_pre_topc @ X12)
% 0.50/0.69           | ~ (v2_pre_topc @ X12)
% 0.50/0.69           | ((k1_tops_1 @ X12 @ X11) != (X11))
% 0.50/0.69           | (v3_pre_topc @ X11 @ X12)))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.50/0.69  thf('44', plain,
% 0.50/0.69      (![X11 : $i, X12 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.69          | ~ (l1_pre_topc @ X12)
% 0.50/0.69          | ~ (v2_pre_topc @ X12)
% 0.50/0.69          | ((k1_tops_1 @ X12 @ X11) != (X11))
% 0.50/0.69          | (v3_pre_topc @ X11 @ X12))),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['36', '43'])).
% 0.50/0.69  thf('45', plain,
% 0.50/0.69      (((v3_pre_topc @ sk_B @ sk_A)
% 0.50/0.69        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.50/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.69        | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['34', '44'])).
% 0.50/0.69  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('48', plain,
% 0.50/0.69      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.50/0.69      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.50/0.69  thf('49', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf(t44_tops_1, axiom,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( l1_pre_topc @ A ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.50/0.69  thf('50', plain,
% 0.50/0.69      (![X7 : $i, X8 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.50/0.69          | (r1_tarski @ (k1_tops_1 @ X8 @ X7) @ X7)
% 0.50/0.69          | ~ (l1_pre_topc @ X8))),
% 0.50/0.69      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.50/0.69  thf('51', plain,
% 0.50/0.69      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['49', '50'])).
% 0.50/0.69  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('53', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.50/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.50/0.69  thf('54', plain,
% 0.50/0.69      (![X4 : $i, X6 : $i]:
% 0.50/0.69         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.50/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.69  thf('55', plain,
% 0.50/0.69      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.69        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.50/0.69  thf('56', plain,
% 0.50/0.69      (![X1 : $i, X3 : $i]:
% 0.50/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.50/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.69  thf('57', plain,
% 0.50/0.69      (![X23 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69          | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A)
% 0.50/0.69          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('58', plain,
% 0.50/0.69      ((![X23 : $i]:
% 0.50/0.69          (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('split', [status(esa)], ['57'])).
% 0.50/0.69  thf('59', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.69              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['56', '58'])).
% 0.50/0.69  thf('60', plain,
% 0.50/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.69         ((r2_hidden @ X16 @ X17) | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('61', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (sk_D @ (sk_C @ X0 @ sk_B)))))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['59', '60'])).
% 0.50/0.69  thf('62', plain,
% 0.50/0.69      ((![X23 : $i]:
% 0.50/0.69          (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))) | 
% 0.50/0.69       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('split', [status(esa)], ['57'])).
% 0.50/0.69  thf('63', plain,
% 0.50/0.69      ((![X23 : $i]:
% 0.50/0.69          (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)],
% 0.50/0.69                ['3', '14', '17', '18', '31', '62'])).
% 0.50/0.69  thf('64', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (sk_D @ (sk_C @ X0 @ sk_B))))),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.50/0.69  thf('65', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('66', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.69              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['56', '58'])).
% 0.50/0.69  thf('67', plain,
% 0.50/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.69         ((v3_pre_topc @ X17 @ X19) | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('68', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.50/0.69  thf('69', plain,
% 0.50/0.69      ((![X23 : $i]:
% 0.50/0.69          (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)],
% 0.50/0.69                ['3', '14', '17', '18', '31', '62'])).
% 0.50/0.69  thf('70', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.50/0.69  thf('71', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.69              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['56', '58'])).
% 0.50/0.69  thf('72', plain,
% 0.50/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.69         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.50/0.69          | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('73', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.69              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['71', '72'])).
% 0.50/0.69  thf(t56_tops_1, axiom,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( l1_pre_topc @ A ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69           ( ![C:$i]:
% 0.50/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.69               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.50/0.69                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.50/0.69  thf('74', plain,
% 0.50/0.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.69          | ~ (v3_pre_topc @ X13 @ X14)
% 0.50/0.69          | ~ (r1_tarski @ X13 @ X15)
% 0.50/0.69          | (r1_tarski @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.50/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.69          | ~ (l1_pre_topc @ X14))),
% 0.50/0.69      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.50/0.69  thf('75', plain,
% 0.50/0.69      ((![X0 : $i, X1 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | ~ (l1_pre_topc @ sk_A)
% 0.50/0.69           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (k1_tops_1 @ sk_A @ X1))
% 0.50/0.69           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)
% 0.50/0.69           | ~ (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['73', '74'])).
% 0.50/0.69  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.69  thf('77', plain,
% 0.50/0.69      ((![X0 : $i, X1 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (k1_tops_1 @ sk_A @ X1))
% 0.50/0.69           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)
% 0.50/0.69           | ~ (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('demod', [status(thm)], ['75', '76'])).
% 0.50/0.69  thf('78', plain,
% 0.50/0.69      ((![X23 : $i]:
% 0.50/0.69          (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)],
% 0.50/0.69                ['3', '14', '17', '18', '31', '62'])).
% 0.50/0.69  thf('79', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (k1_tops_1 @ sk_A @ X1))
% 0.50/0.69          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)
% 0.50/0.69          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 0.50/0.69  thf('80', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)
% 0.50/0.69          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (k1_tops_1 @ sk_A @ X1))
% 0.50/0.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | (r1_tarski @ sk_B @ X0))),
% 0.50/0.69      inference('sup-', [status(thm)], ['70', '79'])).
% 0.50/0.69  thf('81', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.69          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (k1_tops_1 @ sk_A @ X1))
% 0.50/0.69          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)
% 0.50/0.69          | (r1_tarski @ sk_B @ X0))),
% 0.50/0.69      inference('simplify', [status(thm)], ['80'])).
% 0.50/0.69  thf('82', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 0.50/0.69          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.69             (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['65', '81'])).
% 0.50/0.69  thf('83', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 0.50/0.69              (sk_C @ X0 @ sk_B) @ sk_B @ sk_A)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['56', '58'])).
% 0.50/0.69  thf('84', plain,
% 0.50/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.69         ((r1_tarski @ X17 @ X18) | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('85', plain,
% 0.50/0.69      ((![X0 : $i]:
% 0.50/0.69          ((r1_tarski @ sk_B @ X0)
% 0.50/0.69           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)))
% 0.50/0.69         <= ((![X23 : $i]:
% 0.50/0.69                (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69                 | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['83', '84'])).
% 0.50/0.69  thf('86', plain,
% 0.50/0.69      ((![X23 : $i]:
% 0.50/0.69          (~ (r2_hidden @ X23 @ sk_B)
% 0.50/0.69           | (zip_tseitin_0 @ (sk_D @ X23) @ X23 @ sk_B @ sk_A)))),
% 0.50/0.69      inference('sat_resolution*', [status(thm)],
% 0.50/0.69                ['3', '14', '17', '18', '31', '62'])).
% 0.50/0.69  thf('87', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B))),
% 0.50/0.69      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.50/0.69  thf('88', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.69          | (r1_tarski @ sk_B @ X0))),
% 0.50/0.69      inference('clc', [status(thm)], ['82', '87'])).
% 0.50/0.69  thf('89', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.69          | (r2_hidden @ X0 @ X2)
% 0.50/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.69  thf('90', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.69          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C @ X0 @ sk_B))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['88', '89'])).
% 0.50/0.69  thf('91', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r1_tarski @ sk_B @ X0)
% 0.50/0.69          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.69          | (r1_tarski @ sk_B @ X0))),
% 0.50/0.69      inference('sup-', [status(thm)], ['64', '90'])).
% 0.50/0.69  thf('92', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.69          | (r1_tarski @ sk_B @ X0))),
% 0.50/0.69      inference('simplify', [status(thm)], ['91'])).
% 0.50/0.69  thf('93', plain,
% 0.50/0.69      (![X1 : $i, X3 : $i]:
% 0.50/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.50/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.69  thf('94', plain,
% 0.50/0.69      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.69        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['92', '93'])).
% 0.50/0.69  thf('95', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.50/0.69      inference('simplify', [status(thm)], ['94'])).
% 0.50/0.69  thf('96', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.50/0.69      inference('demod', [status(thm)], ['55', '95'])).
% 0.50/0.69  thf('97', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.50/0.69      inference('demod', [status(thm)], ['48', '96'])).
% 0.50/0.69  thf('98', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.50/0.69      inference('simplify', [status(thm)], ['97'])).
% 0.50/0.69  thf('99', plain, ($false), inference('demod', [status(thm)], ['33', '98'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
