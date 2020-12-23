%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9m4sIqK3pg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:22 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  181 (2018 expanded)
%              Number of leaves         :   27 ( 545 expanded)
%              Depth                    :   21
%              Number of atoms          : 1673 (31744 expanded)
%              Number of equality atoms :   65 (1196 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

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

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('5',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('8',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) )
    | ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference(simpl_trail,[status(thm)],['5','14'])).

thf('16',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = sk_C_1 )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
      = sk_C_1 )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('23',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_C_1 )
      | ( ( k1_tops_1 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ~ ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('40',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_tops_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
       != k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference(simpl_trail,[status(thm)],['5','14'])).

thf('44',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        = ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('47',plain,
    ( ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','50','51'])).

thf('53',plain,
    ( ( ( v2_tops_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_C_1 )
       != k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','52'])).

thf('54',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_C_1 )
      | ( v2_tops_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','53'])).

thf('55',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
      = sk_C_1 )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('56',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_C_1 )
      | ( v2_tops_1 @ sk_C_1 @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( v2_tops_1 @ sk_C_1 @ sk_A )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('59',plain,
    ( ( ( v2_tops_1 @ sk_C_1 @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ ( sk_B @ sk_C_1 ) ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( r1_tarski @ X27 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['60'])).

thf('76',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['67','68'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('80',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','77','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ~ ! [X27: $i] :
          ( ( X27 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X27 @ sk_A )
          | ~ ( r1_tarski @ X27 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['61','94','95'])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['61','94','97'])).

thf('99',plain,
    ( ( v2_tops_1 @ sk_C_1 @ sk_A )
    | ~ ( r1_tarski @ sk_C_1 @ ( sk_B @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['59','96','98'])).

thf('100',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('101',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('102',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        = k1_xboole_0 )
      | ~ ( v2_tops_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        = k1_xboole_0 )
      | ~ ( v2_tops_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C_1 )
      = sk_C_1 )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('106',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['61','94','95'])).

thf('107',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['61','94','97'])).

thf('108',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['105','106','107'])).

thf('110',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['105','106','107'])).

thf('111',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v2_tops_1 @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','108','109','110'])).

thf('112',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['112'])).

thf('114',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['112'])).

thf('115',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['61','94','114'])).

thf('116',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['113','115'])).

thf('117',plain,
    ( ~ ( v2_tops_1 @ sk_C_1 @ sk_A )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['111','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['61','94','97'])).

thf('119',plain,(
    ~ ( v2_tops_1 @ sk_C_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['99','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('123',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['105','106','107'])).

thf('128',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['105','106','107'])).

thf('129',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['105','106','107'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['61','94','97'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['121','132'])).

thf('134',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['92'])).

thf('135',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('136',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['61','94','135'])).

thf('137',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['134','136'])).

thf('138',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('139',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('141',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['61','94'])).

thf('146',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['144','145'])).

thf('147',plain,(
    r1_tarski @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['133','137','146'])).

thf('148',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('150',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ X0 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['120','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9m4sIqK3pg
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 687 iterations in 0.217s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.68  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(t86_tops_1, conjecture,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.45/0.68             ( ![C:$i]:
% 0.45/0.68               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.45/0.68                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i]:
% 0.45/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68          ( ![B:$i]:
% 0.45/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68              ( ( v2_tops_1 @ B @ A ) <=>
% 0.45/0.68                ( ![C:$i]:
% 0.45/0.68                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.45/0.68                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.45/0.68      inference('split', [status(esa)], ['0'])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf(t55_tops_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( l1_pre_topc @ B ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68               ( ![D:$i]:
% 0.45/0.68                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.68                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.45/0.68                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.45/0.68                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.45/0.68                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68          | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68          | ((k1_tops_1 @ X21 @ X22) = (X22))
% 0.45/0.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68          | ~ (l1_pre_topc @ X24)
% 0.45/0.68          | ~ (v2_pre_topc @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      ((![X21 : $i, X22 : $i]:
% 0.45/0.68          (~ (l1_pre_topc @ X21)
% 0.45/0.68           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68           | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68           | ((k1_tops_1 @ X21 @ X22) = (X22))))
% 0.45/0.68         <= ((![X21 : $i, X22 : $i]:
% 0.45/0.68                (~ (l1_pre_topc @ X21)
% 0.45/0.68                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68                 | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68                 | ((k1_tops_1 @ X21 @ X22) = (X22)))))),
% 0.45/0.68      inference('split', [status(esa)], ['4'])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68          | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68          | ((k1_tops_1 @ X21 @ X22) = (X22))
% 0.45/0.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68          | ~ (l1_pre_topc @ X24)
% 0.45/0.68          | ~ (v2_pre_topc @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      ((![X23 : $i, X24 : $i]:
% 0.45/0.68          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68           | ~ (l1_pre_topc @ X24)
% 0.45/0.68           | ~ (v2_pre_topc @ X24)))
% 0.45/0.68         <= ((![X23 : $i, X24 : $i]:
% 0.45/0.68                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68                 | ~ (l1_pre_topc @ X24)
% 0.45/0.68                 | ~ (v2_pre_topc @ X24))))),
% 0.45/0.68      inference('split', [status(esa)], ['7'])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.45/0.68         <= ((![X23 : $i, X24 : $i]:
% 0.45/0.68                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68                 | ~ (l1_pre_topc @ X24)
% 0.45/0.68                 | ~ (v2_pre_topc @ X24))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['6', '8'])).
% 0.45/0.68  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (~
% 0.45/0.68       (![X23 : $i, X24 : $i]:
% 0.45/0.68          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68           | ~ (l1_pre_topc @ X24)
% 0.45/0.68           | ~ (v2_pre_topc @ X24)))),
% 0.45/0.68      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      ((![X21 : $i, X22 : $i]:
% 0.45/0.68          (~ (l1_pre_topc @ X21)
% 0.45/0.68           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68           | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68           | ((k1_tops_1 @ X21 @ X22) = (X22)))) | 
% 0.45/0.68       (![X23 : $i, X24 : $i]:
% 0.45/0.68          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.68           | ~ (l1_pre_topc @ X24)
% 0.45/0.68           | ~ (v2_pre_topc @ X24)))),
% 0.45/0.68      inference('split', [status(esa)], ['7'])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      ((![X21 : $i, X22 : $i]:
% 0.45/0.68          (~ (l1_pre_topc @ X21)
% 0.45/0.68           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68           | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68           | ((k1_tops_1 @ X21 @ X22) = (X22))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['12', '13'])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68          | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68          | ((k1_tops_1 @ X21 @ X22) = (X22)))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['5', '14'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))
% 0.45/0.68         | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.45/0.68         | ~ (l1_pre_topc @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['3', '15'])).
% 0.45/0.68  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))
% 0.45/0.68         | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      ((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '18'])).
% 0.45/0.68  thf(t7_xboole_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf(t44_tops_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.68          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.45/0.68          | ~ (l1_pre_topc @ X17))),
% 0.45/0.68      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.68         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.68  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.68  thf(d3_tarski, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.68          | (r2_hidden @ X0 @ X2)
% 0.45/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((r2_hidden @ X0 @ sk_C_1)
% 0.45/0.68           | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (((((k1_tops_1 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.45/0.68         | (r2_hidden @ (sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) @ sk_C_1)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['20', '27'])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      ((((r2_hidden @ (sk_B @ sk_C_1) @ sk_C_1)
% 0.45/0.68         | ((k1_tops_1 @ sk_A @ sk_C_1) = (k1_xboole_0))))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['19', '28'])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf(t3_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i]:
% 0.45/0.68         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.68  thf(t1_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.68       ( r1_tarski @ A @ C ) ))).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.68         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.68          | ~ (r1_tarski @ X6 @ X7)
% 0.45/0.68          | (r1_tarski @ X5 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.45/0.68           | ~ (r1_tarski @ sk_C_1 @ X0)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['32', '35'])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X9 : $i, X11 : $i]:
% 0.45/0.68         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf(t84_tops_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.45/0.68             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ((k1_tops_1 @ X26 @ X25) != (k1_xboole_0))
% 0.45/0.68          | (v2_tops_1 @ X25 @ X26)
% 0.45/0.68          | ~ (l1_pre_topc @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.68         | (v2_tops_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.45/0.68         | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)) != (k1_xboole_0))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.68  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X21)
% 0.45/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.68          | ~ (v3_pre_topc @ X22 @ X21)
% 0.45/0.68          | ((k1_tops_1 @ X21 @ X22) = (X22)))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['5', '14'])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.45/0.68           = (k1_tops_1 @ sk_A @ sk_C_1))
% 0.45/0.68         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.45/0.68         | ~ (l1_pre_topc @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf(fc9_tops_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.45/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.68       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (![X14 : $i, X15 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X14)
% 0.45/0.68          | ~ (v2_pre_topc @ X14)
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.68          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      ((((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.45/0.68         | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68         | ~ (l1_pre_topc @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.68  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.45/0.68  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.45/0.68          = (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['44', '50', '51'])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      ((((v2_tops_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.45/0.68         | ((k1_tops_1 @ sk_A @ sk_C_1) != (k1_xboole_0))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['40', '41', '52'])).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.68         | (r2_hidden @ (sk_B @ sk_C_1) @ sk_C_1)
% 0.45/0.68         | (v2_tops_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['29', '53'])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      ((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '18'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.68         | (r2_hidden @ (sk_B @ sk_C_1) @ sk_C_1)
% 0.45/0.68         | (v2_tops_1 @ sk_C_1 @ sk_A)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      ((((v2_tops_1 @ sk_C_1 @ sk_A) | (r2_hidden @ (sk_B @ sk_C_1) @ sk_C_1)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.68  thf(t7_ordinal1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.45/0.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      ((((v2_tops_1 @ sk_C_1 @ sk_A) | ~ (r1_tarski @ sk_C_1 @ (sk_B @ sk_C_1))))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.68  thf('60', plain,
% 0.45/0.68      (![X27 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68          | ((X27) = (k1_xboole_0))
% 0.45/0.68          | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68          | ~ (r1_tarski @ X27 @ sk_B_1)
% 0.45/0.68          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('61', plain,
% 0.45/0.68      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.45/0.68       (![X27 : $i]:
% 0.45/0.68          (((X27) = (k1_xboole_0))
% 0.45/0.68           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68           | ~ (r1_tarski @ X27 @ sk_B_1)))),
% 0.45/0.68      inference('split', [status(esa)], ['60'])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('63', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i]:
% 0.45/0.68         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('64', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.68  thf('65', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('66', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.68          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.45/0.68          | ~ (l1_pre_topc @ X17))),
% 0.45/0.68      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.68  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('69', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.45/0.68      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.68  thf('70', plain,
% 0.45/0.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.68         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.68          | ~ (r1_tarski @ X6 @ X7)
% 0.45/0.68          | (r1_tarski @ X5 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.68  thf('71', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 0.45/0.68          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.68  thf('72', plain,
% 0.45/0.68      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['64', '71'])).
% 0.45/0.68  thf('73', plain,
% 0.45/0.68      (![X9 : $i, X11 : $i]:
% 0.45/0.68         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('74', plain,
% 0.45/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.68  thf('75', plain,
% 0.45/0.68      ((![X27 : $i]:
% 0.45/0.68          (((X27) = (k1_xboole_0))
% 0.45/0.68           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68           | ~ (r1_tarski @ X27 @ sk_B_1)))
% 0.45/0.68         <= ((![X27 : $i]:
% 0.45/0.68                (((X27) = (k1_xboole_0))
% 0.45/0.68                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.45/0.68      inference('split', [status(esa)], ['60'])).
% 0.45/0.68  thf('76', plain,
% 0.45/0.68      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.45/0.68         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.45/0.68         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.45/0.68         <= ((![X27 : $i]:
% 0.45/0.68                (((X27) = (k1_xboole_0))
% 0.45/0.68                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.68  thf('77', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.45/0.68      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.68  thf('78', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('79', plain,
% 0.45/0.68      (![X14 : $i, X15 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X14)
% 0.45/0.68          | ~ (v2_pre_topc @ X14)
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.45/0.68          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.45/0.68  thf('80', plain,
% 0.45/0.68      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.45/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['78', '79'])).
% 0.45/0.68  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('83', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.45/0.68      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.45/0.68  thf('84', plain,
% 0.45/0.68      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.45/0.68         <= ((![X27 : $i]:
% 0.45/0.68                (((X27) = (k1_xboole_0))
% 0.45/0.68                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.45/0.68      inference('demod', [status(thm)], ['76', '77', '83'])).
% 0.45/0.68  thf('85', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('86', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ((k1_tops_1 @ X26 @ X25) != (k1_xboole_0))
% 0.45/0.68          | (v2_tops_1 @ X25 @ X26)
% 0.45/0.68          | ~ (l1_pre_topc @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.45/0.68  thf('87', plain,
% 0.45/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.45/0.68        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.68  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('89', plain,
% 0.45/0.68      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.45/0.68        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['87', '88'])).
% 0.45/0.68  thf('90', plain,
% 0.45/0.68      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.45/0.68         <= ((![X27 : $i]:
% 0.45/0.68                (((X27) = (k1_xboole_0))
% 0.45/0.68                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['84', '89'])).
% 0.45/0.68  thf('91', plain,
% 0.45/0.68      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.45/0.68         <= ((![X27 : $i]:
% 0.45/0.68                (((X27) = (k1_xboole_0))
% 0.45/0.68                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['90'])).
% 0.45/0.68  thf('92', plain,
% 0.45/0.68      (((r1_tarski @ sk_C_1 @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('93', plain,
% 0.45/0.68      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.68      inference('split', [status(esa)], ['92'])).
% 0.45/0.68  thf('94', plain,
% 0.45/0.68      (~
% 0.45/0.68       (![X27 : $i]:
% 0.45/0.68          (((X27) = (k1_xboole_0))
% 0.45/0.68           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.45/0.68           | ~ (r1_tarski @ X27 @ sk_B_1))) | 
% 0.45/0.68       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['91', '93'])).
% 0.45/0.68  thf('95', plain,
% 0.45/0.68      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('split', [status(esa)], ['0'])).
% 0.45/0.68  thf('96', plain, (((v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '95'])).
% 0.45/0.68  thf('97', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.45/0.68       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('split', [status(esa)], ['2'])).
% 0.45/0.68  thf('98', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '97'])).
% 0.45/0.68  thf('99', plain,
% 0.45/0.68      (((v2_tops_1 @ sk_C_1 @ sk_A) | ~ (r1_tarski @ sk_C_1 @ (sk_B @ sk_C_1)))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['59', '96', '98'])).
% 0.45/0.68  thf('100', plain,
% 0.45/0.68      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('101', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ~ (v2_tops_1 @ X25 @ X26)
% 0.45/0.68          | ((k1_tops_1 @ X26 @ X25) = (k1_xboole_0))
% 0.45/0.68          | ~ (l1_pre_topc @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.45/0.68  thf('102', plain,
% 0.45/0.68      (((~ (l1_pre_topc @ sk_A)
% 0.45/0.68         | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)) = (k1_xboole_0))
% 0.45/0.68         | ~ (v2_tops_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['100', '101'])).
% 0.45/0.68  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('104', plain,
% 0.45/0.68      (((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)) = (k1_xboole_0))
% 0.45/0.68         | ~ (v2_tops_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.68  thf('105', plain,
% 0.45/0.68      ((((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1)))
% 0.45/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.45/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '18'])).
% 0.45/0.68  thf('106', plain, (((v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '95'])).
% 0.45/0.68  thf('107', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '97'])).
% 0.45/0.68  thf('108', plain, (((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['105', '106', '107'])).
% 0.45/0.68  thf('109', plain, (((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['105', '106', '107'])).
% 0.45/0.68  thf('110', plain, (((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['105', '106', '107'])).
% 0.45/0.68  thf('111', plain,
% 0.45/0.68      (((((sk_C_1) = (k1_xboole_0)) | ~ (v2_tops_1 @ sk_C_1 @ sk_A)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['104', '108', '109', '110'])).
% 0.45/0.68  thf('112', plain,
% 0.45/0.68      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('113', plain,
% 0.45/0.68      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.45/0.68      inference('split', [status(esa)], ['112'])).
% 0.45/0.68  thf('114', plain,
% 0.45/0.68      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('split', [status(esa)], ['112'])).
% 0.45/0.68  thf('115', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '114'])).
% 0.45/0.68  thf('116', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['113', '115'])).
% 0.45/0.68  thf('117', plain,
% 0.45/0.68      ((~ (v2_tops_1 @ sk_C_1 @ sk_A))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['111', '116'])).
% 0.45/0.68  thf('118', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '97'])).
% 0.45/0.68  thf('119', plain, (~ (v2_tops_1 @ sk_C_1 @ sk_A)),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 0.45/0.68  thf('120', plain, (~ (r1_tarski @ sk_C_1 @ (sk_B @ sk_C_1))),
% 0.45/0.68      inference('clc', [status(thm)], ['99', '119'])).
% 0.45/0.68  thf('121', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('122', plain,
% 0.45/0.68      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf(t48_tops_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68               ( ( r1_tarski @ B @ C ) =>
% 0.45/0.68                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('123', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.68          | ~ (r1_tarski @ X18 @ X20)
% 0.45/0.68          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ (k1_tops_1 @ X19 @ X20))
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.68          | ~ (l1_pre_topc @ X19))),
% 0.45/0.68      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.45/0.68  thf('124', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          (~ (l1_pre_topc @ sk_A)
% 0.45/0.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68           | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.45/0.68              (k1_tops_1 @ sk_A @ X0))
% 0.45/0.68           | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['122', '123'])).
% 0.45/0.68  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('126', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68           | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.45/0.68              (k1_tops_1 @ sk_A @ X0))
% 0.45/0.68           | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.68  thf('127', plain, (((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['105', '106', '107'])).
% 0.45/0.68  thf('128', plain, (((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['105', '106', '107'])).
% 0.45/0.68  thf('129', plain, (((k1_tops_1 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['105', '106', '107'])).
% 0.45/0.68  thf('130', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.68           | ~ (r1_tarski @ sk_C_1 @ X0)))
% 0.45/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.45/0.68  thf('131', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '97'])).
% 0.45/0.68  thf('132', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68          | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.45/0.68          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['130', '131'])).
% 0.45/0.68  thf('133', plain,
% 0.45/0.68      ((~ (r1_tarski @ sk_C_1 @ sk_B_1)
% 0.45/0.68        | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['121', '132'])).
% 0.45/0.68  thf('134', plain,
% 0.45/0.68      (((r1_tarski @ sk_C_1 @ sk_B_1)) <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 0.45/0.68      inference('split', [status(esa)], ['92'])).
% 0.45/0.68  thf('135', plain,
% 0.45/0.68      (((r1_tarski @ sk_C_1 @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('split', [status(esa)], ['92'])).
% 0.45/0.68  thf('136', plain, (((r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94', '135'])).
% 0.45/0.68  thf('137', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['134', '136'])).
% 0.45/0.68  thf('138', plain,
% 0.45/0.68      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.68      inference('split', [status(esa)], ['60'])).
% 0.45/0.68  thf('139', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('140', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.68          | ~ (v2_tops_1 @ X25 @ X26)
% 0.45/0.68          | ((k1_tops_1 @ X26 @ X25) = (k1_xboole_0))
% 0.45/0.68          | ~ (l1_pre_topc @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.45/0.68  thf('141', plain,
% 0.45/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.68        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.45/0.68        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['139', '140'])).
% 0.45/0.68  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('143', plain,
% 0.45/0.68      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.45/0.68        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['141', '142'])).
% 0.45/0.68  thf('144', plain,
% 0.45/0.68      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.45/0.68         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['138', '143'])).
% 0.45/0.68  thf('145', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['61', '94'])).
% 0.45/0.68  thf('146', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['144', '145'])).
% 0.45/0.68  thf('147', plain, ((r1_tarski @ sk_C_1 @ k1_xboole_0)),
% 0.45/0.68      inference('demod', [status(thm)], ['133', '137', '146'])).
% 0.45/0.68  thf('148', plain,
% 0.45/0.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.68         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.68          | ~ (r1_tarski @ X6 @ X7)
% 0.45/0.68          | (r1_tarski @ X5 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.68  thf('149', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r1_tarski @ sk_C_1 @ X0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['147', '148'])).
% 0.45/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.68  thf('150', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.45/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.68  thf('151', plain, (![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)),
% 0.45/0.68      inference('demod', [status(thm)], ['149', '150'])).
% 0.45/0.68  thf('152', plain, ($false), inference('demod', [status(thm)], ['120', '151'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.53/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
