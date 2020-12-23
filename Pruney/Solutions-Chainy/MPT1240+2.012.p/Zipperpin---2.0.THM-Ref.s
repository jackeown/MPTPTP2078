%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jRBL6B9PiL

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:07 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 699 expanded)
%              Number of leaves         :   28 ( 198 expanded)
%              Depth                    :   21
%              Number of atoms          : 1084 (11113 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( r1_tarski @ X27 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X27 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X27 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X27 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X27 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X27 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
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
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X27 ) ) ),
    inference(demod,[status(thm)],['19','20','26'])).

thf('28',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X27 @ sk_A )
          | ~ ( r1_tarski @ X27 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X27 ) )
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k2_pre_topc @ X17 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28','42'])).

thf('63',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

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

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('69',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['72'])).

thf('75',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','28','74'])).

thf('76',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['73','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28','42'])).

thf('79',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['65','66','79'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28','42'])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','28','42'])).

thf('88',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference(simpl_trail,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['53','89'])).

thf('91',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['30','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jRBL6B9PiL
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.70/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.90  % Solved by: fo/fo7.sh
% 0.70/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.90  % done 937 iterations in 0.463s
% 0.70/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.90  % SZS output start Refutation
% 0.70/0.90  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.70/0.90  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.70/0.90  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.70/0.90  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.70/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.90  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.70/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.90  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.90  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.70/0.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.70/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.90  thf(t54_tops_1, conjecture,
% 0.70/0.90    (![A:$i]:
% 0.70/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.90       ( ![B:$i,C:$i]:
% 0.70/0.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.70/0.90             ( ?[D:$i]:
% 0.70/0.90               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.70/0.90                 ( v3_pre_topc @ D @ A ) & 
% 0.70/0.90                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.70/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.90    (~( ![A:$i]:
% 0.70/0.90        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.90          ( ![B:$i,C:$i]:
% 0.70/0.90            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.70/0.90                ( ?[D:$i]:
% 0.70/0.90                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.70/0.90                    ( v3_pre_topc @ D @ A ) & 
% 0.70/0.90                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.70/0.90    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.70/0.90  thf('0', plain,
% 0.70/0.90      (![X27 : $i]:
% 0.70/0.90         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90          | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.70/0.90          | ~ (r1_tarski @ X27 @ sk_C_1)
% 0.70/0.90          | ~ (r2_hidden @ sk_B @ X27)
% 0.70/0.90          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('1', plain,
% 0.70/0.90      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.70/0.90         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('2', plain,
% 0.70/0.90      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))) | 
% 0.70/0.90       (![X27 : $i]:
% 0.70/0.90          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.70/0.90           | ~ (r1_tarski @ X27 @ sk_C_1)
% 0.70/0.90           | ~ (r2_hidden @ sk_B @ X27)))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('3', plain,
% 0.70/0.90      (((r2_hidden @ sk_B @ sk_D)
% 0.70/0.90        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('4', plain,
% 0.70/0.90      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.70/0.90         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.70/0.90      inference('split', [status(esa)], ['3'])).
% 0.70/0.90  thf('5', plain,
% 0.70/0.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(t3_subset, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.90  thf('6', plain,
% 0.70/0.90      (![X11 : $i, X12 : $i]:
% 0.70/0.90         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.90  thf('7', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.70/0.90  thf('8', plain,
% 0.70/0.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(t44_tops_1, axiom,
% 0.70/0.90    (![A:$i]:
% 0.70/0.90     ( ( l1_pre_topc @ A ) =>
% 0.70/0.90       ( ![B:$i]:
% 0.70/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.70/0.90  thf('9', plain,
% 0.70/0.90      (![X22 : $i, X23 : $i]:
% 0.70/0.90         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.70/0.90          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 0.70/0.90          | ~ (l1_pre_topc @ X23))),
% 0.70/0.90      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.70/0.90  thf('10', plain,
% 0.70/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.90        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['8', '9'])).
% 0.70/0.90  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.70/0.90      inference('demod', [status(thm)], ['10', '11'])).
% 0.70/0.90  thf(t1_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.70/0.90       ( r1_tarski @ A @ C ) ))).
% 0.70/0.90  thf('13', plain,
% 0.70/0.90      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.70/0.90         (~ (r1_tarski @ X4 @ X5)
% 0.70/0.90          | ~ (r1_tarski @ X5 @ X6)
% 0.70/0.90          | (r1_tarski @ X4 @ X6))),
% 0.70/0.90      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.70/0.90  thf('14', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.70/0.90          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.70/0.90      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.90  thf('15', plain,
% 0.70/0.90      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['7', '14'])).
% 0.70/0.90  thf('16', plain,
% 0.70/0.90      (![X11 : $i, X13 : $i]:
% 0.70/0.90         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.70/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.90  thf('17', plain,
% 0.70/0.90      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.70/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.90  thf('18', plain,
% 0.70/0.90      ((![X27 : $i]:
% 0.70/0.90          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.70/0.90           | ~ (r1_tarski @ X27 @ sk_C_1)
% 0.70/0.90           | ~ (r2_hidden @ sk_B @ X27)))
% 0.70/0.90         <= ((![X27 : $i]:
% 0.70/0.90                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.70/0.90                 | ~ (r1_tarski @ X27 @ sk_C_1)
% 0.70/0.90                 | ~ (r2_hidden @ sk_B @ X27))))),
% 0.70/0.90      inference('split', [status(esa)], ['0'])).
% 0.70/0.90  thf('19', plain,
% 0.70/0.90      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.70/0.90         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.70/0.90         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.70/0.90         <= ((![X27 : $i]:
% 0.70/0.90                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.70/0.90                 | ~ (r1_tarski @ X27 @ sk_C_1)
% 0.70/0.90                 | ~ (r2_hidden @ sk_B @ X27))))),
% 0.70/0.90      inference('sup-', [status(thm)], ['17', '18'])).
% 0.70/0.90  thf('20', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.70/0.90      inference('demod', [status(thm)], ['10', '11'])).
% 0.70/0.90  thf('21', plain,
% 0.70/0.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(fc9_tops_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.70/0.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.70/0.90       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.70/0.90  thf('22', plain,
% 0.70/0.90      (![X18 : $i, X19 : $i]:
% 0.70/0.90         (~ (l1_pre_topc @ X18)
% 0.70/0.90          | ~ (v2_pre_topc @ X18)
% 0.70/0.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.70/0.90          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 0.70/0.90      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.70/0.90  thf('23', plain,
% 0.70/0.90      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.70/0.90        | ~ (v2_pre_topc @ sk_A)
% 0.70/0.90        | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['21', '22'])).
% 0.70/0.90  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('26', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.70/0.90      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.70/0.90  thf('27', plain,
% 0.70/0.90      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.70/0.90         <= ((![X27 : $i]:
% 0.70/0.90                (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.70/0.90                 | ~ (r1_tarski @ X27 @ sk_C_1)
% 0.70/0.90                 | ~ (r2_hidden @ sk_B @ X27))))),
% 0.70/0.90      inference('demod', [status(thm)], ['19', '20', '26'])).
% 0.70/0.90  thf('28', plain,
% 0.70/0.90      (~
% 0.70/0.90       (![X27 : $i]:
% 0.70/0.90          (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.70/0.90           | ~ (r1_tarski @ X27 @ sk_C_1)
% 0.70/0.90           | ~ (r2_hidden @ sk_B @ X27))) | 
% 0.70/0.90       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['4', '27'])).
% 0.70/0.90  thf('29', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28'])).
% 0.70/0.90  thf('30', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.70/0.90  thf('31', plain,
% 0.70/0.90      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.70/0.90      inference('split', [status(esa)], ['3'])).
% 0.70/0.90  thf('32', plain,
% 0.70/0.90      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.70/0.90       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('split', [status(esa)], ['3'])).
% 0.70/0.90  thf('33', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '32'])).
% 0.70/0.90  thf('34', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.70/0.90  thf('35', plain,
% 0.70/0.90      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('36', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('37', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('split', [status(esa)], ['36'])).
% 0.70/0.90  thf(t48_tops_1, axiom,
% 0.70/0.90    (![A:$i]:
% 0.70/0.90     ( ( l1_pre_topc @ A ) =>
% 0.70/0.90       ( ![B:$i]:
% 0.70/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90           ( ![C:$i]:
% 0.70/0.90             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90               ( ( r1_tarski @ B @ C ) =>
% 0.70/0.90                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.70/0.90  thf('38', plain,
% 0.70/0.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.70/0.90         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.70/0.90          | ~ (r1_tarski @ X24 @ X26)
% 0.70/0.90          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 0.70/0.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.70/0.90          | ~ (l1_pre_topc @ X25))),
% 0.70/0.90      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.70/0.90  thf('39', plain,
% 0.70/0.90      ((![X0 : $i]:
% 0.70/0.90          (~ (l1_pre_topc @ sk_A)
% 0.70/0.90           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.70/0.90           | ~ (r1_tarski @ sk_D @ X0)))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('sup-', [status(thm)], ['37', '38'])).
% 0.70/0.90  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('41', plain,
% 0.70/0.90      ((![X0 : $i]:
% 0.70/0.90          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.70/0.90           | ~ (r1_tarski @ sk_D @ X0)))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('demod', [status(thm)], ['39', '40'])).
% 0.70/0.90  thf('42', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.70/0.90       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('split', [status(esa)], ['36'])).
% 0.70/0.90  thf('43', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.70/0.90  thf('44', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.90          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.70/0.90          | ~ (r1_tarski @ sk_D @ X0))),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.70/0.90  thf('45', plain,
% 0.70/0.90      ((~ (r1_tarski @ sk_D @ sk_C_1)
% 0.70/0.90        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['35', '44'])).
% 0.70/0.90  thf('46', plain,
% 0.70/0.90      (((r1_tarski @ sk_D @ sk_C_1)
% 0.70/0.90        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('47', plain,
% 0.70/0.90      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.70/0.90      inference('split', [status(esa)], ['46'])).
% 0.70/0.90  thf('48', plain,
% 0.70/0.90      (((r1_tarski @ sk_D @ sk_C_1)) | 
% 0.70/0.90       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('split', [status(esa)], ['46'])).
% 0.70/0.90  thf('49', plain, (((r1_tarski @ sk_D @ sk_C_1))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '48'])).
% 0.70/0.90  thf('50', plain, ((r1_tarski @ sk_D @ sk_C_1)),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['47', '49'])).
% 0.70/0.90  thf('51', plain,
% 0.70/0.90      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.70/0.90      inference('demod', [status(thm)], ['45', '50'])).
% 0.70/0.90  thf(d3_tarski, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.90  thf('52', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.90          | (r2_hidden @ X0 @ X2)
% 0.70/0.90          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.90  thf('53', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.70/0.90          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['51', '52'])).
% 0.70/0.90  thf('54', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('split', [status(esa)], ['36'])).
% 0.70/0.90  thf(d1_tops_1, axiom,
% 0.70/0.90    (![A:$i]:
% 0.70/0.90     ( ( l1_pre_topc @ A ) =>
% 0.70/0.90       ( ![B:$i]:
% 0.70/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90           ( ( k1_tops_1 @ A @ B ) =
% 0.70/0.90             ( k3_subset_1 @
% 0.70/0.90               ( u1_struct_0 @ A ) @ 
% 0.70/0.90               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.70/0.90  thf('55', plain,
% 0.70/0.90      (![X16 : $i, X17 : $i]:
% 0.70/0.90         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.70/0.90          | ((k1_tops_1 @ X17 @ X16)
% 0.70/0.90              = (k3_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.70/0.90                 (k2_pre_topc @ X17 @ (k3_subset_1 @ (u1_struct_0 @ X17) @ X16))))
% 0.70/0.90          | ~ (l1_pre_topc @ X17))),
% 0.70/0.90      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.70/0.90  thf('56', plain,
% 0.70/0.90      (((~ (l1_pre_topc @ sk_A)
% 0.70/0.90         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.70/0.90             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.90                (k2_pre_topc @ sk_A @ 
% 0.70/0.90                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('sup-', [status(thm)], ['54', '55'])).
% 0.70/0.90  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('58', plain,
% 0.70/0.90      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.70/0.90          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.90             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('demod', [status(thm)], ['56', '57'])).
% 0.70/0.90  thf('59', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('split', [status(esa)], ['36'])).
% 0.70/0.90  thf(dt_k3_subset_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.90       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.70/0.90  thf('60', plain,
% 0.70/0.90      (![X7 : $i, X8 : $i]:
% 0.70/0.90         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 0.70/0.90          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.70/0.90      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.70/0.90  thf('61', plain,
% 0.70/0.90      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.70/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('sup-', [status(thm)], ['59', '60'])).
% 0.70/0.90  thf('62', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.70/0.90  thf('63', plain,
% 0.70/0.90      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.70/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.70/0.90  thf(t52_pre_topc, axiom,
% 0.70/0.90    (![A:$i]:
% 0.70/0.90     ( ( l1_pre_topc @ A ) =>
% 0.70/0.90       ( ![B:$i]:
% 0.70/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.70/0.90             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.70/0.90               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.70/0.90  thf('64', plain,
% 0.70/0.90      (![X14 : $i, X15 : $i]:
% 0.70/0.90         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.70/0.90          | ~ (v4_pre_topc @ X14 @ X15)
% 0.70/0.90          | ((k2_pre_topc @ X15 @ X14) = (X14))
% 0.70/0.90          | ~ (l1_pre_topc @ X15))),
% 0.70/0.90      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.70/0.90  thf('65', plain,
% 0.70/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.90        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.70/0.90            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.70/0.90        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))),
% 0.70/0.90      inference('sup-', [status(thm)], ['63', '64'])).
% 0.70/0.90  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('67', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('split', [status(esa)], ['36'])).
% 0.70/0.90  thf(t30_tops_1, axiom,
% 0.70/0.90    (![A:$i]:
% 0.70/0.90     ( ( l1_pre_topc @ A ) =>
% 0.70/0.90       ( ![B:$i]:
% 0.70/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.90           ( ( v3_pre_topc @ B @ A ) <=>
% 0.70/0.90             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.70/0.90  thf('68', plain,
% 0.70/0.90      (![X20 : $i, X21 : $i]:
% 0.70/0.90         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.70/0.90          | ~ (v3_pre_topc @ X20 @ X21)
% 0.70/0.90          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.70/0.90          | ~ (l1_pre_topc @ X21))),
% 0.70/0.90      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.70/0.90  thf('69', plain,
% 0.70/0.90      (((~ (l1_pre_topc @ sk_A)
% 0.70/0.90         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.70/0.90         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('sup-', [status(thm)], ['67', '68'])).
% 0.70/0.90  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('71', plain,
% 0.70/0.90      ((((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.70/0.90         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('demod', [status(thm)], ['69', '70'])).
% 0.70/0.90  thf('72', plain,
% 0.70/0.90      (((v3_pre_topc @ sk_D @ sk_A)
% 0.70/0.90        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf('73', plain,
% 0.70/0.90      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.70/0.90      inference('split', [status(esa)], ['72'])).
% 0.70/0.90  thf('74', plain,
% 0.70/0.90      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.70/0.90       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.70/0.90      inference('split', [status(esa)], ['72'])).
% 0.70/0.90  thf('75', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '74'])).
% 0.70/0.90  thf('76', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['73', '75'])).
% 0.70/0.90  thf('77', plain,
% 0.70/0.90      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('demod', [status(thm)], ['71', '76'])).
% 0.70/0.90  thf('78', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.70/0.90  thf('79', plain,
% 0.70/0.90      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 0.70/0.90  thf('80', plain,
% 0.70/0.90      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.70/0.90         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.70/0.90      inference('demod', [status(thm)], ['65', '66', '79'])).
% 0.70/0.90  thf('81', plain,
% 0.70/0.90      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.70/0.90          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.90             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('demod', [status(thm)], ['58', '80'])).
% 0.70/0.90  thf('82', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.70/0.90  thf('83', plain,
% 0.70/0.90      (((k1_tops_1 @ sk_A @ sk_D)
% 0.70/0.90         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.90            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.70/0.90  thf('84', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('split', [status(esa)], ['36'])).
% 0.70/0.90  thf(involutiveness_k3_subset_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.90       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.70/0.90  thf('85', plain,
% 0.70/0.90      (![X9 : $i, X10 : $i]:
% 0.70/0.90         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 0.70/0.90          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.70/0.90      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.70/0.90  thf('86', plain,
% 0.70/0.90      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.90          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.70/0.90         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.70/0.90      inference('sup-', [status(thm)], ['84', '85'])).
% 0.70/0.90  thf('87', plain,
% 0.70/0.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.90      inference('sat_resolution*', [status(thm)], ['2', '28', '42'])).
% 0.70/0.90  thf('88', plain,
% 0.70/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.90         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 0.70/0.90      inference('simpl_trail', [status(thm)], ['86', '87'])).
% 0.70/0.90  thf('89', plain, (((k1_tops_1 @ sk_A @ sk_D) = (sk_D))),
% 0.70/0.90      inference('sup+', [status(thm)], ['83', '88'])).
% 0.70/0.90  thf('90', plain,
% 0.70/0.90      (![X0 : $i]:
% 0.70/0.90         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.70/0.90          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.70/0.90      inference('demod', [status(thm)], ['53', '89'])).
% 0.70/0.90  thf('91', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['34', '90'])).
% 0.70/0.90  thf('92', plain, ($false), inference('demod', [status(thm)], ['30', '91'])).
% 0.70/0.90  
% 0.70/0.90  % SZS output end Refutation
% 0.70/0.90  
% 0.74/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
