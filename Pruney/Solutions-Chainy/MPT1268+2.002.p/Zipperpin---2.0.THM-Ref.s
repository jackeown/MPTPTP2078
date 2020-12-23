%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K1ODs7OJVd

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:15 EST 2020

% Result     : Theorem 4.72s
% Output     : Refutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 168 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  914 (2331 expanded)
%              Number of equality atoms :   44 (  98 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf('0',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X31 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X31 @ sk_A )
      | ~ ( r1_tarski @ X31 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X31: $i] :
        ( ( X31 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X31 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X31 @ sk_A )
      | ~ ( r1_tarski @ X31 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X31: $i] :
        ( ( X31 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_B ) )
   <= ! [X31: $i] :
        ( ( X31 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X31: $i] :
        ( ( X31 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('29',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X31: $i] :
        ( ( X31 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k1_tops_1 @ X30 @ X29 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X31: $i] :
        ( ( X31 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X31: $i] :
        ( ( X31 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ~ ! [X31: $i] :
          ( ( X31 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X31 @ sk_A )
          | ~ ( r1_tarski @ X31 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tops_1 @ X29 @ X30 )
      | ( ( k1_tops_1 @ X30 @ X29 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['41'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['49'])).

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

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( r1_tarski @ X26 @ X28 )
      | ( r1_tarski @ X26 @ ( k1_tops_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('70',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('73',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','46','48','50','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K1ODs7OJVd
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.72/4.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.72/4.89  % Solved by: fo/fo7.sh
% 4.72/4.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.72/4.89  % done 7495 iterations in 4.426s
% 4.72/4.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.72/4.89  % SZS output start Refutation
% 4.72/4.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.72/4.89  thf(sk_A_type, type, sk_A: $i).
% 4.72/4.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.72/4.89  thf(sk_B_type, type, sk_B: $i).
% 4.72/4.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.72/4.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.72/4.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.72/4.89  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 4.72/4.89  thf(sk_C_type, type, sk_C: $i).
% 4.72/4.89  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.72/4.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.72/4.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.72/4.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.72/4.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.72/4.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.72/4.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.72/4.89  thf(t86_tops_1, conjecture,
% 4.72/4.89    (![A:$i]:
% 4.72/4.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.72/4.89       ( ![B:$i]:
% 4.72/4.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89           ( ( v2_tops_1 @ B @ A ) <=>
% 4.72/4.89             ( ![C:$i]:
% 4.72/4.89               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 4.72/4.89                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 4.72/4.89  thf(zf_stmt_0, negated_conjecture,
% 4.72/4.89    (~( ![A:$i]:
% 4.72/4.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.72/4.89          ( ![B:$i]:
% 4.72/4.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89              ( ( v2_tops_1 @ B @ A ) <=>
% 4.72/4.89                ( ![C:$i]:
% 4.72/4.89                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 4.72/4.89                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 4.72/4.89    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 4.72/4.89  thf('0', plain,
% 4.72/4.89      (![X31 : $i]:
% 4.72/4.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89          | ((X31) = (k1_xboole_0))
% 4.72/4.89          | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89          | ~ (r1_tarski @ X31 @ sk_B)
% 4.72/4.89          | (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('1', plain,
% 4.72/4.89      ((![X31 : $i]:
% 4.72/4.89          (((X31) = (k1_xboole_0))
% 4.72/4.89           | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89           | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89           | ~ (r1_tarski @ X31 @ sk_B))) | 
% 4.72/4.89       ((v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('split', [status(esa)], ['0'])).
% 4.72/4.89  thf('2', plain,
% 4.72/4.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf(t44_tops_1, axiom,
% 4.72/4.89    (![A:$i]:
% 4.72/4.89     ( ( l1_pre_topc @ A ) =>
% 4.72/4.89       ( ![B:$i]:
% 4.72/4.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 4.72/4.89  thf('3', plain,
% 4.72/4.89      (![X24 : $i, X25 : $i]:
% 4.72/4.89         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 4.72/4.89          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ X24)
% 4.72/4.89          | ~ (l1_pre_topc @ X25))),
% 4.72/4.89      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.72/4.89  thf('4', plain,
% 4.72/4.89      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 4.72/4.89      inference('sup-', [status(thm)], ['2', '3'])).
% 4.72/4.89  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('6', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.72/4.89      inference('demod', [status(thm)], ['4', '5'])).
% 4.72/4.89  thf(t28_xboole_1, axiom,
% 4.72/4.89    (![A:$i,B:$i]:
% 4.72/4.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.72/4.89  thf('7', plain,
% 4.72/4.89      (![X6 : $i, X7 : $i]:
% 4.72/4.89         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 4.72/4.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.72/4.89  thf('8', plain,
% 4.72/4.89      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 4.72/4.89         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.72/4.89      inference('sup-', [status(thm)], ['6', '7'])).
% 4.72/4.89  thf(commutativity_k2_tarski, axiom,
% 4.72/4.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.72/4.89  thf('9', plain,
% 4.72/4.89      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 4.72/4.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.72/4.89  thf(t12_setfam_1, axiom,
% 4.72/4.89    (![A:$i,B:$i]:
% 4.72/4.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.72/4.89  thf('10', plain,
% 4.72/4.89      (![X17 : $i, X18 : $i]:
% 4.72/4.89         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 4.72/4.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.72/4.89  thf('11', plain,
% 4.72/4.89      (![X0 : $i, X1 : $i]:
% 4.72/4.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 4.72/4.89      inference('sup+', [status(thm)], ['9', '10'])).
% 4.72/4.89  thf('12', plain,
% 4.72/4.89      (![X17 : $i, X18 : $i]:
% 4.72/4.89         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 4.72/4.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.72/4.89  thf('13', plain,
% 4.72/4.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.72/4.89      inference('sup+', [status(thm)], ['11', '12'])).
% 4.72/4.89  thf('14', plain,
% 4.72/4.89      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.72/4.89         = (k1_tops_1 @ sk_A @ sk_B))),
% 4.72/4.89      inference('demod', [status(thm)], ['8', '13'])).
% 4.72/4.89  thf('15', plain,
% 4.72/4.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf(t3_subset, axiom,
% 4.72/4.89    (![A:$i,B:$i]:
% 4.72/4.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.72/4.89  thf('16', plain,
% 4.72/4.89      (![X19 : $i, X20 : $i]:
% 4.72/4.89         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 4.72/4.89      inference('cnf', [status(esa)], [t3_subset])).
% 4.72/4.89  thf('17', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.72/4.89      inference('sup-', [status(thm)], ['15', '16'])).
% 4.72/4.89  thf(t108_xboole_1, axiom,
% 4.72/4.89    (![A:$i,B:$i,C:$i]:
% 4.72/4.89     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 4.72/4.89  thf('18', plain,
% 4.72/4.89      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.72/4.89         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 4.72/4.89      inference('cnf', [status(esa)], [t108_xboole_1])).
% 4.72/4.89  thf('19', plain,
% 4.72/4.89      (![X0 : $i]:
% 4.72/4.89         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 4.72/4.89      inference('sup-', [status(thm)], ['17', '18'])).
% 4.72/4.89  thf('20', plain,
% 4.72/4.89      (![X19 : $i, X21 : $i]:
% 4.72/4.89         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 4.72/4.89      inference('cnf', [status(esa)], [t3_subset])).
% 4.72/4.89  thf('21', plain,
% 4.72/4.89      (![X0 : $i]:
% 4.72/4.89         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 4.72/4.89          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('sup-', [status(thm)], ['19', '20'])).
% 4.72/4.89  thf('22', plain,
% 4.72/4.89      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.72/4.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('sup+', [status(thm)], ['14', '21'])).
% 4.72/4.89  thf('23', plain,
% 4.72/4.89      (![X31 : $i]:
% 4.72/4.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89          | ((X31) = (k1_xboole_0))
% 4.72/4.89          | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89          | ~ (r1_tarski @ X31 @ sk_B)
% 4.72/4.89          | (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('24', plain,
% 4.72/4.89      ((![X31 : $i]:
% 4.72/4.89          (((X31) = (k1_xboole_0))
% 4.72/4.89           | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89           | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89           | ~ (r1_tarski @ X31 @ sk_B)))
% 4.72/4.89         <= ((![X31 : $i]:
% 4.72/4.89                (((X31) = (k1_xboole_0))
% 4.72/4.89                 | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89                 | ~ (r1_tarski @ X31 @ sk_B))))),
% 4.72/4.89      inference('split', [status(esa)], ['23'])).
% 4.72/4.89  thf('25', plain,
% 4.72/4.89      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 4.72/4.89         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.72/4.89         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 4.72/4.89         <= ((![X31 : $i]:
% 4.72/4.89                (((X31) = (k1_xboole_0))
% 4.72/4.89                 | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89                 | ~ (r1_tarski @ X31 @ sk_B))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['22', '24'])).
% 4.72/4.89  thf('26', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.72/4.89      inference('demod', [status(thm)], ['4', '5'])).
% 4.72/4.89  thf('27', plain,
% 4.72/4.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf(fc9_tops_1, axiom,
% 4.72/4.89    (![A:$i,B:$i]:
% 4.72/4.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.72/4.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.72/4.89       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 4.72/4.89  thf('28', plain,
% 4.72/4.89      (![X22 : $i, X23 : $i]:
% 4.72/4.89         (~ (l1_pre_topc @ X22)
% 4.72/4.89          | ~ (v2_pre_topc @ X22)
% 4.72/4.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.72/4.89          | (v3_pre_topc @ (k1_tops_1 @ X22 @ X23) @ X22))),
% 4.72/4.89      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.72/4.89  thf('29', plain,
% 4.72/4.89      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.72/4.89        | ~ (v2_pre_topc @ sk_A)
% 4.72/4.89        | ~ (l1_pre_topc @ sk_A))),
% 4.72/4.89      inference('sup-', [status(thm)], ['27', '28'])).
% 4.72/4.89  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('32', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 4.72/4.89      inference('demod', [status(thm)], ['29', '30', '31'])).
% 4.72/4.89  thf('33', plain,
% 4.72/4.89      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 4.72/4.89         <= ((![X31 : $i]:
% 4.72/4.89                (((X31) = (k1_xboole_0))
% 4.72/4.89                 | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89                 | ~ (r1_tarski @ X31 @ sk_B))))),
% 4.72/4.89      inference('demod', [status(thm)], ['25', '26', '32'])).
% 4.72/4.89  thf('34', plain,
% 4.72/4.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf(t84_tops_1, axiom,
% 4.72/4.89    (![A:$i]:
% 4.72/4.89     ( ( l1_pre_topc @ A ) =>
% 4.72/4.89       ( ![B:$i]:
% 4.72/4.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89           ( ( v2_tops_1 @ B @ A ) <=>
% 4.72/4.89             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 4.72/4.89  thf('35', plain,
% 4.72/4.89      (![X29 : $i, X30 : $i]:
% 4.72/4.89         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.72/4.89          | ((k1_tops_1 @ X30 @ X29) != (k1_xboole_0))
% 4.72/4.89          | (v2_tops_1 @ X29 @ X30)
% 4.72/4.89          | ~ (l1_pre_topc @ X30))),
% 4.72/4.89      inference('cnf', [status(esa)], [t84_tops_1])).
% 4.72/4.89  thf('36', plain,
% 4.72/4.89      ((~ (l1_pre_topc @ sk_A)
% 4.72/4.89        | (v2_tops_1 @ sk_B @ sk_A)
% 4.72/4.89        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 4.72/4.89      inference('sup-', [status(thm)], ['34', '35'])).
% 4.72/4.89  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('38', plain,
% 4.72/4.89      (((v2_tops_1 @ sk_B @ sk_A)
% 4.72/4.89        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 4.72/4.89      inference('demod', [status(thm)], ['36', '37'])).
% 4.72/4.89  thf('39', plain,
% 4.72/4.89      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 4.72/4.89         <= ((![X31 : $i]:
% 4.72/4.89                (((X31) = (k1_xboole_0))
% 4.72/4.89                 | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89                 | ~ (r1_tarski @ X31 @ sk_B))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['33', '38'])).
% 4.72/4.89  thf('40', plain,
% 4.72/4.89      (((v2_tops_1 @ sk_B @ sk_A))
% 4.72/4.89         <= ((![X31 : $i]:
% 4.72/4.89                (((X31) = (k1_xboole_0))
% 4.72/4.89                 | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89                 | ~ (r1_tarski @ X31 @ sk_B))))),
% 4.72/4.89      inference('simplify', [status(thm)], ['39'])).
% 4.72/4.89  thf('41', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('42', plain,
% 4.72/4.89      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 4.72/4.89      inference('split', [status(esa)], ['41'])).
% 4.72/4.89  thf('43', plain,
% 4.72/4.89      (~
% 4.72/4.89       (![X31 : $i]:
% 4.72/4.89          (((X31) = (k1_xboole_0))
% 4.72/4.89           | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89           | ~ (v3_pre_topc @ X31 @ sk_A)
% 4.72/4.89           | ~ (r1_tarski @ X31 @ sk_B))) | 
% 4.72/4.89       ((v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('sup-', [status(thm)], ['40', '42'])).
% 4.72/4.89  thf('44', plain,
% 4.72/4.89      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('split', [status(esa)], ['41'])).
% 4.72/4.89  thf('45', plain,
% 4.72/4.89      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('46', plain,
% 4.72/4.89      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('split', [status(esa)], ['45'])).
% 4.72/4.89  thf('47', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('48', plain,
% 4.72/4.89      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('split', [status(esa)], ['47'])).
% 4.72/4.89  thf('49', plain,
% 4.72/4.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('50', plain,
% 4.72/4.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 4.72/4.89       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('split', [status(esa)], ['49'])).
% 4.72/4.89  thf('51', plain,
% 4.72/4.89      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 4.72/4.89      inference('split', [status(esa)], ['0'])).
% 4.72/4.89  thf('52', plain,
% 4.72/4.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('53', plain,
% 4.72/4.89      (![X29 : $i, X30 : $i]:
% 4.72/4.89         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.72/4.89          | ~ (v2_tops_1 @ X29 @ X30)
% 4.72/4.89          | ((k1_tops_1 @ X30 @ X29) = (k1_xboole_0))
% 4.72/4.89          | ~ (l1_pre_topc @ X30))),
% 4.72/4.89      inference('cnf', [status(esa)], [t84_tops_1])).
% 4.72/4.89  thf('54', plain,
% 4.72/4.89      ((~ (l1_pre_topc @ sk_A)
% 4.72/4.89        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 4.72/4.89        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('sup-', [status(thm)], ['52', '53'])).
% 4.72/4.89  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('56', plain,
% 4.72/4.89      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 4.72/4.89        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 4.72/4.89      inference('demod', [status(thm)], ['54', '55'])).
% 4.72/4.89  thf('57', plain,
% 4.72/4.89      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 4.72/4.89         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 4.72/4.89      inference('sup-', [status(thm)], ['51', '56'])).
% 4.72/4.89  thf('58', plain,
% 4.72/4.89      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 4.72/4.89      inference('split', [status(esa)], ['41'])).
% 4.72/4.89  thf('59', plain,
% 4.72/4.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('60', plain,
% 4.72/4.89      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 4.72/4.89      inference('split', [status(esa)], ['45'])).
% 4.72/4.89  thf('61', plain,
% 4.72/4.89      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.72/4.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('split', [status(esa)], ['49'])).
% 4.72/4.89  thf(t56_tops_1, axiom,
% 4.72/4.89    (![A:$i]:
% 4.72/4.89     ( ( l1_pre_topc @ A ) =>
% 4.72/4.89       ( ![B:$i]:
% 4.72/4.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89           ( ![C:$i]:
% 4.72/4.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.72/4.89               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 4.72/4.89                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 4.72/4.89  thf('62', plain,
% 4.72/4.89      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.72/4.89         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 4.72/4.89          | ~ (v3_pre_topc @ X26 @ X27)
% 4.72/4.89          | ~ (r1_tarski @ X26 @ X28)
% 4.72/4.89          | (r1_tarski @ X26 @ (k1_tops_1 @ X27 @ X28))
% 4.72/4.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 4.72/4.89          | ~ (l1_pre_topc @ X27))),
% 4.72/4.89      inference('cnf', [status(esa)], [t56_tops_1])).
% 4.72/4.89  thf('63', plain,
% 4.72/4.89      ((![X0 : $i]:
% 4.72/4.89          (~ (l1_pre_topc @ sk_A)
% 4.72/4.89           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 4.72/4.89           | ~ (r1_tarski @ sk_C @ X0)
% 4.72/4.89           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 4.72/4.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['61', '62'])).
% 4.72/4.89  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 4.72/4.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.89  thf('65', plain,
% 4.72/4.89      ((![X0 : $i]:
% 4.72/4.89          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.72/4.89           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 4.72/4.89           | ~ (r1_tarski @ sk_C @ X0)
% 4.72/4.89           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 4.72/4.89         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('demod', [status(thm)], ['63', '64'])).
% 4.72/4.89  thf('66', plain,
% 4.72/4.89      ((![X0 : $i]:
% 4.72/4.89          (~ (r1_tarski @ sk_C @ X0)
% 4.72/4.89           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 4.72/4.89           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 4.72/4.89         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.72/4.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['60', '65'])).
% 4.72/4.89  thf('67', plain,
% 4.72/4.89      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 4.72/4.89         | ~ (r1_tarski @ sk_C @ sk_B)))
% 4.72/4.89         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.72/4.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['59', '66'])).
% 4.72/4.89  thf('68', plain,
% 4.72/4.89      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.72/4.89         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 4.72/4.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.72/4.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['58', '67'])).
% 4.72/4.89  thf('69', plain,
% 4.72/4.89      (((r1_tarski @ sk_C @ k1_xboole_0))
% 4.72/4.89         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 4.72/4.89             ((r1_tarski @ sk_C @ sk_B)) & 
% 4.72/4.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.72/4.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('sup+', [status(thm)], ['57', '68'])).
% 4.72/4.89  thf(t3_xboole_1, axiom,
% 4.72/4.89    (![A:$i]:
% 4.72/4.89     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.72/4.89  thf('70', plain,
% 4.72/4.89      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 4.72/4.89      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.72/4.89  thf('71', plain,
% 4.72/4.89      ((((sk_C) = (k1_xboole_0)))
% 4.72/4.89         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 4.72/4.89             ((r1_tarski @ sk_C @ sk_B)) & 
% 4.72/4.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.72/4.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['69', '70'])).
% 4.72/4.89  thf('72', plain,
% 4.72/4.89      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 4.72/4.89      inference('split', [status(esa)], ['47'])).
% 4.72/4.89  thf('73', plain,
% 4.72/4.89      ((((sk_C) != (sk_C)))
% 4.72/4.89         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 4.72/4.89             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 4.72/4.89             ((r1_tarski @ sk_C @ sk_B)) & 
% 4.72/4.89             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 4.72/4.89             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.72/4.89      inference('sup-', [status(thm)], ['71', '72'])).
% 4.72/4.89  thf('74', plain,
% 4.72/4.89      (~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 4.72/4.89       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 4.72/4.89       ~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 4.72/4.89       (((sk_C) = (k1_xboole_0)))),
% 4.72/4.89      inference('simplify', [status(thm)], ['73'])).
% 4.72/4.89  thf('75', plain, ($false),
% 4.72/4.89      inference('sat_resolution*', [status(thm)],
% 4.72/4.89                ['1', '43', '44', '46', '48', '50', '74'])).
% 4.72/4.89  
% 4.72/4.89  % SZS output end Refutation
% 4.72/4.89  
% 4.72/4.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
