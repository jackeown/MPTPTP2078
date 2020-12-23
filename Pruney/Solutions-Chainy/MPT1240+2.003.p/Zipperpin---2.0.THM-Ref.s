%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y8qbqJEj7e

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:05 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 783 expanded)
%              Number of leaves         :   33 ( 227 expanded)
%              Depth                    :   22
%              Number of atoms          : 1283 (11336 expanded)
%              Number of equality atoms :   33 (  88 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t54_tops_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
            <=> ? [D: $i] :
                  ( ( r2_hidden @ B @ D )
                  & ( r1_tarski @ D @ C )
                  & ( v3_pre_topc @ D @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_tops_1])).

thf('0',plain,(
    ! [X47: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X47 @ sk_A )
      | ~ ( r1_tarski @ X47 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X47 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ! [X47: $i] :
        ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X47 @ sk_A )
        | ~ ( r1_tarski @ X47 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X47 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X43 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X47: $i] :
        ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X47 @ sk_A )
        | ~ ( r1_tarski @ X47 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X47 ) )
   <= ! [X47: $i] :
        ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X47 @ sk_A )
        | ~ ( r1_tarski @ X47 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X47 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X47: $i] :
        ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X47 @ sk_A )
        | ~ ( r1_tarski @ X47 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X47 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['10','11'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('22',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X38 @ X39 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('23',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ! [X47: $i] :
        ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X47 @ sk_A )
        | ~ ( r1_tarski @ X47 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X47 ) ) ),
    inference(demod,[status(thm)],['19','20','26'])).

thf('28',plain,
    ( ~ ! [X47: $i] :
          ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X47 @ sk_A )
          | ~ ( r1_tarski @ X47 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X47 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','28','32'])).

thf('34',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r1_tarski @ ( k1_tops_1 @ X45 @ X44 ) @ ( k1_tops_1 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['36'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['46'])).

thf('49',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','28','48'])).

thf('50',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['47','49'])).

thf('51',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k2_pre_topc @ X37 @ ( k3_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 ) ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('56',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('64',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('66',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('71',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X15 @ X14 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28','42'])).

thf('81',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('83',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 ) @ X41 )
      | ( v4_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['88'])).

thf('91',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','28','90'])).

thf('92',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['89','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['87','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('96',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v4_pre_topc @ X34 @ X35 )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('102',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28','42'])).

thf('104',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('106',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','106'])).

thf('108',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['30','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y8qbqJEj7e
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.16  % Solved by: fo/fo7.sh
% 0.90/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.16  % done 1660 iterations in 0.702s
% 0.90/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.16  % SZS output start Refutation
% 0.90/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.16  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.90/1.16  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.16  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.16  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.90/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.16  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.90/1.16  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.16  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.90/1.16  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.16  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.16  thf(t54_tops_1, conjecture,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.16       ( ![B:$i,C:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.90/1.16             ( ?[D:$i]:
% 0.90/1.16               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.90/1.16                 ( v3_pre_topc @ D @ A ) & 
% 0.90/1.16                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.16    (~( ![A:$i]:
% 0.90/1.16        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.16          ( ![B:$i,C:$i]:
% 0.90/1.16            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.90/1.16                ( ?[D:$i]:
% 0.90/1.16                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.90/1.16                    ( v3_pre_topc @ D @ A ) & 
% 0.90/1.16                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.90/1.16    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.90/1.16  thf('0', plain,
% 0.90/1.16      (![X47 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16          | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.90/1.16          | ~ (r1_tarski @ X47 @ sk_C_1)
% 0.90/1.16          | ~ (r2_hidden @ sk_B @ X47)
% 0.90/1.16          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('1', plain,
% 0.90/1.16      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.90/1.16         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.90/1.16      inference('split', [status(esa)], ['0'])).
% 0.90/1.16  thf('2', plain,
% 0.90/1.16      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))) | 
% 0.90/1.16       (![X47 : $i]:
% 0.90/1.16          (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16           | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.90/1.16           | ~ (r1_tarski @ X47 @ sk_C_1)
% 0.90/1.16           | ~ (r2_hidden @ sk_B @ X47)))),
% 0.90/1.16      inference('split', [status(esa)], ['0'])).
% 0.90/1.16  thf('3', plain,
% 0.90/1.16      (((r2_hidden @ sk_B @ sk_D)
% 0.90/1.16        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('4', plain,
% 0.90/1.16      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.90/1.16         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.90/1.16      inference('split', [status(esa)], ['3'])).
% 0.90/1.16  thf('5', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(t3_subset, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.16  thf('6', plain,
% 0.90/1.16      (![X31 : $i, X32 : $i]:
% 0.90/1.16         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.90/1.16      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.16  thf('7', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.16  thf('8', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(t44_tops_1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( l1_pre_topc @ A ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.90/1.16  thf('9', plain,
% 0.90/1.16      (![X42 : $i, X43 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.90/1.16          | (r1_tarski @ (k1_tops_1 @ X43 @ X42) @ X42)
% 0.90/1.16          | ~ (l1_pre_topc @ X43))),
% 0.90/1.16      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.90/1.16  thf('10', plain,
% 0.90/1.16      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.16        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.90/1.16      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.16  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.90/1.16      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.16  thf(t1_xboole_1, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i]:
% 0.90/1.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.90/1.16       ( r1_tarski @ A @ C ) ))).
% 0.90/1.16  thf('13', plain,
% 0.90/1.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.16         (~ (r1_tarski @ X7 @ X8)
% 0.90/1.16          | ~ (r1_tarski @ X8 @ X9)
% 0.90/1.16          | (r1_tarski @ X7 @ X9))),
% 0.90/1.16      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.90/1.16  thf('14', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.90/1.16          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.16  thf('15', plain,
% 0.90/1.16      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['7', '14'])).
% 0.90/1.16  thf('16', plain,
% 0.90/1.16      (![X31 : $i, X33 : $i]:
% 0.90/1.16         ((m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X33)) | ~ (r1_tarski @ X31 @ X33))),
% 0.90/1.16      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.16  thf('17', plain,
% 0.90/1.16      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.90/1.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['15', '16'])).
% 0.90/1.16  thf('18', plain,
% 0.90/1.16      ((![X47 : $i]:
% 0.90/1.16          (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16           | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.90/1.16           | ~ (r1_tarski @ X47 @ sk_C_1)
% 0.90/1.16           | ~ (r2_hidden @ sk_B @ X47)))
% 0.90/1.16         <= ((![X47 : $i]:
% 0.90/1.16                (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16                 | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.90/1.16                 | ~ (r1_tarski @ X47 @ sk_C_1)
% 0.90/1.16                 | ~ (r2_hidden @ sk_B @ X47))))),
% 0.90/1.16      inference('split', [status(esa)], ['0'])).
% 0.90/1.16  thf('19', plain,
% 0.90/1.16      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.90/1.16         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.90/1.16         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.90/1.16         <= ((![X47 : $i]:
% 0.90/1.16                (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16                 | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.90/1.16                 | ~ (r1_tarski @ X47 @ sk_C_1)
% 0.90/1.16                 | ~ (r2_hidden @ sk_B @ X47))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.16  thf('20', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.90/1.16      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.16  thf('21', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf(fc9_tops_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.90/1.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.16       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.90/1.16  thf('22', plain,
% 0.90/1.16      (![X38 : $i, X39 : $i]:
% 0.90/1.16         (~ (l1_pre_topc @ X38)
% 0.90/1.16          | ~ (v2_pre_topc @ X38)
% 0.90/1.16          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.90/1.16          | (v3_pre_topc @ (k1_tops_1 @ X38 @ X39) @ X38))),
% 0.90/1.16      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.90/1.16  thf('23', plain,
% 0.90/1.16      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.90/1.16        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.16        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.16  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('26', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.90/1.16      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.90/1.16  thf('27', plain,
% 0.90/1.16      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.90/1.16         <= ((![X47 : $i]:
% 0.90/1.16                (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16                 | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.90/1.16                 | ~ (r1_tarski @ X47 @ sk_C_1)
% 0.90/1.16                 | ~ (r2_hidden @ sk_B @ X47))))),
% 0.90/1.16      inference('demod', [status(thm)], ['19', '20', '26'])).
% 0.90/1.16  thf('28', plain,
% 0.90/1.16      (~
% 0.90/1.16       (![X47 : $i]:
% 0.90/1.16          (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16           | ~ (v3_pre_topc @ X47 @ sk_A)
% 0.90/1.16           | ~ (r1_tarski @ X47 @ sk_C_1)
% 0.90/1.16           | ~ (r2_hidden @ sk_B @ X47))) | 
% 0.90/1.16       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['4', '27'])).
% 0.90/1.16  thf('29', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['2', '28'])).
% 0.90/1.16  thf('30', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.90/1.16  thf('31', plain,
% 0.90/1.16      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.90/1.16      inference('split', [status(esa)], ['3'])).
% 0.90/1.16  thf('32', plain,
% 0.90/1.16      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.90/1.16       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('split', [status(esa)], ['3'])).
% 0.90/1.16  thf('33', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['2', '28', '32'])).
% 0.90/1.16  thf('34', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.90/1.16  thf('35', plain,
% 0.90/1.16      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('36', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('37', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('split', [status(esa)], ['36'])).
% 0.90/1.16  thf(t48_tops_1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( l1_pre_topc @ A ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16           ( ![C:$i]:
% 0.90/1.16             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16               ( ( r1_tarski @ B @ C ) =>
% 0.90/1.16                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.90/1.16  thf('38', plain,
% 0.90/1.16      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.90/1.16          | ~ (r1_tarski @ X44 @ X46)
% 0.90/1.16          | (r1_tarski @ (k1_tops_1 @ X45 @ X44) @ (k1_tops_1 @ X45 @ X46))
% 0.90/1.16          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.90/1.16          | ~ (l1_pre_topc @ X45))),
% 0.90/1.16      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.90/1.16  thf('39', plain,
% 0.90/1.16      ((![X0 : $i]:
% 0.90/1.16          (~ (l1_pre_topc @ sk_A)
% 0.90/1.16           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.90/1.16           | ~ (r1_tarski @ sk_D @ X0)))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.16  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('41', plain,
% 0.90/1.16      ((![X0 : $i]:
% 0.90/1.16          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.90/1.16           | ~ (r1_tarski @ sk_D @ X0)))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('demod', [status(thm)], ['39', '40'])).
% 0.90/1.16  thf('42', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.90/1.16       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('split', [status(esa)], ['36'])).
% 0.90/1.16  thf('43', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.90/1.16  thf('44', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.90/1.16          | ~ (r1_tarski @ sk_D @ X0))),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.90/1.16  thf('45', plain,
% 0.90/1.16      ((~ (r1_tarski @ sk_D @ sk_C_1)
% 0.90/1.16        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['35', '44'])).
% 0.90/1.16  thf('46', plain,
% 0.90/1.16      (((r1_tarski @ sk_D @ sk_C_1)
% 0.90/1.16        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('47', plain,
% 0.90/1.16      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.90/1.16      inference('split', [status(esa)], ['46'])).
% 0.90/1.16  thf('48', plain,
% 0.90/1.16      (((r1_tarski @ sk_D @ sk_C_1)) | 
% 0.90/1.16       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('split', [status(esa)], ['46'])).
% 0.90/1.16  thf('49', plain, (((r1_tarski @ sk_D @ sk_C_1))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['2', '28', '48'])).
% 0.90/1.16  thf('50', plain, ((r1_tarski @ sk_D @ sk_C_1)),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['47', '49'])).
% 0.90/1.16  thf('51', plain,
% 0.90/1.16      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.90/1.16      inference('demod', [status(thm)], ['45', '50'])).
% 0.90/1.16  thf(d3_tarski, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.16       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.16  thf('52', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.16         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.16          | (r2_hidden @ X0 @ X2)
% 0.90/1.16          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.16      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.16  thf('53', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.90/1.16          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.16  thf('54', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('split', [status(esa)], ['36'])).
% 0.90/1.16  thf(d1_tops_1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( l1_pre_topc @ A ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16           ( ( k1_tops_1 @ A @ B ) =
% 0.90/1.16             ( k3_subset_1 @
% 0.90/1.16               ( u1_struct_0 @ A ) @ 
% 0.90/1.16               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.90/1.16  thf('55', plain,
% 0.90/1.16      (![X36 : $i, X37 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.90/1.16          | ((k1_tops_1 @ X37 @ X36)
% 0.90/1.16              = (k3_subset_1 @ (u1_struct_0 @ X37) @ 
% 0.90/1.16                 (k2_pre_topc @ X37 @ (k3_subset_1 @ (u1_struct_0 @ X37) @ X36))))
% 0.90/1.16          | ~ (l1_pre_topc @ X37))),
% 0.90/1.16      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.90/1.16  thf('56', plain,
% 0.90/1.16      (((~ (l1_pre_topc @ sk_A)
% 0.90/1.16         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.16             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16                (k2_pre_topc @ sk_A @ 
% 0.90/1.16                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.16  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('58', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('split', [status(esa)], ['36'])).
% 0.90/1.16  thf(d5_subset_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.16       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.90/1.16  thf('59', plain,
% 0.90/1.16      (![X10 : $i, X11 : $i]:
% 0.90/1.16         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.90/1.16          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.90/1.16      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.90/1.16  thf('60', plain,
% 0.90/1.16      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 0.90/1.16          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.16  thf('61', plain,
% 0.90/1.16      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.16          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('demod', [status(thm)], ['56', '57', '60'])).
% 0.90/1.16  thf('62', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('split', [status(esa)], ['36'])).
% 0.90/1.16  thf(involutiveness_k3_subset_1, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.16       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.90/1.16  thf('63', plain,
% 0.90/1.16      (![X17 : $i, X18 : $i]:
% 0.90/1.16         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 0.90/1.16          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.90/1.16      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.90/1.16  thf('64', plain,
% 0.90/1.16      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['62', '63'])).
% 0.90/1.16  thf('65', plain,
% 0.90/1.16      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 0.90/1.16          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.16  thf('66', plain,
% 0.90/1.16      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('demod', [status(thm)], ['64', '65'])).
% 0.90/1.16  thf(d10_xboole_0, axiom,
% 0.90/1.16    (![A:$i,B:$i]:
% 0.90/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.16  thf('67', plain,
% 0.90/1.16      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.90/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.16  thf('68', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.90/1.16      inference('simplify', [status(thm)], ['67'])).
% 0.90/1.16  thf('69', plain,
% 0.90/1.16      (![X31 : $i, X33 : $i]:
% 0.90/1.16         ((m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X33)) | ~ (r1_tarski @ X31 @ X33))),
% 0.90/1.16      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.16  thf('70', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['68', '69'])).
% 0.90/1.16  thf(dt_k7_subset_1, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.16       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.90/1.16  thf('71', plain,
% 0.90/1.16      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.90/1.16          | (m1_subset_1 @ (k7_subset_1 @ X15 @ X14 @ X16) @ 
% 0.90/1.16             (k1_zfmisc_1 @ X15)))),
% 0.90/1.16      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.90/1.16  thf('72', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['70', '71'])).
% 0.90/1.16  thf('73', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['68', '69'])).
% 0.90/1.16  thf(redefinition_k7_subset_1, axiom,
% 0.90/1.16    (![A:$i,B:$i,C:$i]:
% 0.90/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.16       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.90/1.16  thf('74', plain,
% 0.90/1.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.90/1.16          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.90/1.16      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.16  thf('75', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.90/1.16      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.16  thf('76', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['72', '75'])).
% 0.90/1.16  thf('77', plain,
% 0.90/1.16      (![X10 : $i, X11 : $i]:
% 0.90/1.16         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.90/1.16          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.90/1.16      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.90/1.16  thf('78', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.90/1.16           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.16  thf('79', plain,
% 0.90/1.16      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('demod', [status(thm)], ['66', '78'])).
% 0.90/1.16  thf('80', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.90/1.16  thf('81', plain,
% 0.90/1.16      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.90/1.16  thf('82', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['72', '75'])).
% 0.90/1.16  thf(t29_tops_1, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( l1_pre_topc @ A ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16           ( ( v4_pre_topc @ B @ A ) <=>
% 0.90/1.16             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.90/1.16  thf('83', plain,
% 0.90/1.16      (![X40 : $i, X41 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.90/1.16          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X41) @ X40) @ X41)
% 0.90/1.16          | (v4_pre_topc @ X40 @ X41)
% 0.90/1.16          | ~ (l1_pre_topc @ X41))),
% 0.90/1.16      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.90/1.16  thf('84', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (~ (l1_pre_topc @ X0)
% 0.90/1.16          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.90/1.16          | ~ (v3_pre_topc @ 
% 0.90/1.16               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.90/1.16                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.90/1.16               X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['82', '83'])).
% 0.90/1.16  thf('85', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.90/1.16           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.16  thf('86', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (~ (l1_pre_topc @ X0)
% 0.90/1.16          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.90/1.16          | ~ (v3_pre_topc @ 
% 0.90/1.16               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.90/1.16                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.90/1.16               X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['84', '85'])).
% 0.90/1.16  thf('87', plain,
% 0.90/1.16      ((~ (v3_pre_topc @ sk_D @ sk_A)
% 0.90/1.16        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.90/1.16        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['81', '86'])).
% 0.90/1.16  thf('88', plain,
% 0.90/1.16      (((v3_pre_topc @ sk_D @ sk_A)
% 0.90/1.16        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('89', plain,
% 0.90/1.16      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.90/1.16      inference('split', [status(esa)], ['88'])).
% 0.90/1.16  thf('90', plain,
% 0.90/1.16      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.90/1.16       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.90/1.16      inference('split', [status(esa)], ['88'])).
% 0.90/1.16  thf('91', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['2', '28', '90'])).
% 0.90/1.16  thf('92', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['89', '91'])).
% 0.90/1.16  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('94', plain,
% 0.90/1.16      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 0.90/1.16      inference('demod', [status(thm)], ['87', '92', '93'])).
% 0.90/1.16  thf('95', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.16      inference('demod', [status(thm)], ['72', '75'])).
% 0.90/1.16  thf(t52_pre_topc, axiom,
% 0.90/1.16    (![A:$i]:
% 0.90/1.16     ( ( l1_pre_topc @ A ) =>
% 0.90/1.16       ( ![B:$i]:
% 0.90/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.16           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.90/1.16             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.90/1.16               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.90/1.16  thf('96', plain,
% 0.90/1.16      (![X34 : $i, X35 : $i]:
% 0.90/1.16         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.16          | ~ (v4_pre_topc @ X34 @ X35)
% 0.90/1.16          | ((k2_pre_topc @ X35 @ X34) = (X34))
% 0.90/1.16          | ~ (l1_pre_topc @ X35))),
% 0.90/1.16      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.90/1.16  thf('97', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         (~ (l1_pre_topc @ X0)
% 0.90/1.16          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.90/1.16              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.90/1.16          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.90/1.16      inference('sup-', [status(thm)], ['95', '96'])).
% 0.90/1.16  thf('98', plain,
% 0.90/1.16      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.90/1.16          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.90/1.16        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.16      inference('sup-', [status(thm)], ['94', '97'])).
% 0.90/1.16  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.16  thf('100', plain,
% 0.90/1.16      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.90/1.16         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.90/1.16      inference('demod', [status(thm)], ['98', '99'])).
% 0.90/1.16  thf('101', plain,
% 0.90/1.16      (![X0 : $i, X1 : $i]:
% 0.90/1.16         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.90/1.16           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.16      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.16  thf('102', plain,
% 0.90/1.16      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.16          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 0.90/1.16         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.16      inference('demod', [status(thm)], ['61', '100', '101'])).
% 0.90/1.16  thf('103', plain,
% 0.90/1.16      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.16      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.90/1.16  thf('104', plain,
% 0.90/1.16      (((k1_tops_1 @ sk_A @ sk_D)
% 0.90/1.16         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['102', '103'])).
% 0.90/1.16  thf('105', plain,
% 0.90/1.16      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.16         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 0.90/1.16      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.90/1.16  thf('106', plain, (((k1_tops_1 @ sk_A @ sk_D) = (sk_D))),
% 0.90/1.16      inference('sup+', [status(thm)], ['104', '105'])).
% 0.90/1.16  thf('107', plain,
% 0.90/1.16      (![X0 : $i]:
% 0.90/1.16         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.90/1.16          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.90/1.16      inference('demod', [status(thm)], ['53', '106'])).
% 0.90/1.16  thf('108', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.90/1.16      inference('sup-', [status(thm)], ['34', '107'])).
% 0.90/1.16  thf('109', plain, ($false), inference('demod', [status(thm)], ['30', '108'])).
% 0.90/1.16  
% 0.90/1.16  % SZS output end Refutation
% 0.90/1.16  
% 0.90/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
