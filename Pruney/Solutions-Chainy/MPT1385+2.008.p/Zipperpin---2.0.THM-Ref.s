%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IgTE9l5Sgq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:59 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 429 expanded)
%              Number of leaves         :   30 ( 130 expanded)
%              Depth                    :   33
%              Number of atoms          : 1097 (6200 expanded)
%              Number of equality atoms :    8 (  23 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t10_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( m2_connsp_2 @ C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X5 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m2_connsp_2 @ X27 @ X26 @ X25 )
      | ( r1_tarski @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('18',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X5 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ( m2_connsp_2 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('50',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('51',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('63',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['23','61','62'])).

thf('64',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['21','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['15','64'])).

thf('66',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','69'])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf('83',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['23','61'])).

thf('84',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('89',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','92'])).

thf('94',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('97',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IgTE9l5Sgq
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 191 iterations in 0.117s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.56  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.36/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.56  thf(t10_connsp_2, conjecture,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( m2_connsp_2 @
% 0.36/0.56                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.36/0.56                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i]:
% 0.36/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.56            ( l1_pre_topc @ A ) ) =>
% 0.36/0.56          ( ![B:$i]:
% 0.36/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56              ( ![C:$i]:
% 0.36/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                  ( ( m2_connsp_2 @
% 0.36/0.56                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.36/0.56                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.36/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(d1_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.56  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.56  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t2_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         ((r2_hidden @ X7 @ X8)
% 0.36/0.56          | (v1_xboole_0 @ X8)
% 0.36/0.56          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf(t63_subset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.56       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X5 : $i, X6 : $i]:
% 0.36/0.56         ((m1_subset_1 @ (k1_tarski @ X5) @ (k1_zfmisc_1 @ X6))
% 0.36/0.56          | ~ (r2_hidden @ X5 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf(d2_connsp_2, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.56                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.56          | ~ (m2_connsp_2 @ X27 @ X26 @ X25)
% 0.36/0.56          | (r1_tarski @ X25 @ (k1_tops_1 @ X26 @ X27))
% 0.36/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.56          | ~ (l1_pre_topc @ X26)
% 0.36/0.56          | ~ (v2_pre_topc @ X26))),
% 0.36/0.56      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.56  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '14'])).
% 0.36/0.56  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X20 : $i, X21 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ X20)
% 0.36/0.56          | ~ (m1_subset_1 @ X21 @ X20)
% 0.36/0.56          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.36/0.56        | (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.56      inference('split', [status(esa)], ['19'])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['18', '20'])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.36/0.56        | ~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.36/0.56       ~
% 0.36/0.56       ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.56      inference('split', [status(esa)], ['22'])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('split', [status(esa)], ['19'])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(d1_connsp_2, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.56                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.36/0.56          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.36/0.56          | (r2_hidden @ X22 @ (k1_tops_1 @ X23 @ X24))
% 0.36/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.36/0.56          | ~ (l1_pre_topc @ X23)
% 0.36/0.56          | ~ (v2_pre_topc @ X23)
% 0.36/0.56          | (v2_struct_0 @ X23))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.56  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '30'])).
% 0.36/0.56  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X5 : $i, X6 : $i]:
% 0.36/0.56         ((m1_subset_1 @ (k1_tarski @ X5) @ (k1_zfmisc_1 @ X6))
% 0.36/0.56          | ~ (r2_hidden @ X5 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.36/0.56         (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.56  thf(t3_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      (![X9 : $i, X10 : $i]:
% 0.36/0.56         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.56          | ~ (r1_tarski @ X25 @ (k1_tops_1 @ X26 @ X27))
% 0.36/0.56          | (m2_connsp_2 @ X27 @ X26 @ X25)
% 0.36/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.56          | ~ (l1_pre_topc @ X26)
% 0.36/0.56          | ~ (v2_pre_topc @ X26))),
% 0.36/0.56      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.56  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['39', '45'])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.56      inference('split', [status(esa)], ['22'])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.56             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['48', '51'])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.56             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['52'])).
% 0.36/0.56  thf(fc2_struct_0, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      (![X19 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.36/0.56          | ~ (l1_struct_0 @ X19)
% 0.36/0.56          | (v2_struct_0 @ X19))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.56             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.56  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(dt_l1_pre_topc, axiom,
% 0.36/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.56  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_A))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.56             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['55', '58'])).
% 0.36/0.56  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.36/0.56       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.36/0.56       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('split', [status(esa)], ['19'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['23', '61', '62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['21', '63'])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.36/0.56      inference('clc', [status(thm)], ['15', '64'])).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      (![X9 : $i, X11 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.56  thf(t4_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.56       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X12 @ X13)
% 0.36/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.36/0.56          | (m1_subset_1 @ X12 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | (m1_subset_1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      (((m1_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['3', '69'])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         ((r2_hidden @ X7 @ X8)
% 0.36/0.56          | (v1_xboole_0 @ X8)
% 0.36/0.56          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.56  thf('72', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.36/0.56          | ~ (r2_hidden @ X22 @ (k1_tops_1 @ X23 @ X24))
% 0.36/0.56          | (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.36/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.36/0.56          | ~ (l1_pre_topc @ X23)
% 0.36/0.56          | ~ (v2_pre_topc @ X23)
% 0.36/0.56          | (v2_struct_0 @ X23))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.56  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('78', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.36/0.56  thf('79', plain,
% 0.36/0.56      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['72', '78'])).
% 0.36/0.56  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.36/0.56        | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.56  thf('82', plain,
% 0.36/0.56      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.56         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.56      inference('split', [status(esa)], ['22'])).
% 0.36/0.56  thf('83', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['23', '61'])).
% 0.36/0.56  thf('84', plain, (~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      (((v2_struct_0 @ sk_A)
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['81', '84'])).
% 0.36/0.56  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('87', plain,
% 0.36/0.56      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('clc', [status(thm)], ['85', '86'])).
% 0.36/0.56  thf('88', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.56  thf(t5_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X15 @ X16)
% 0.36/0.56          | ~ (v1_xboole_0 @ X17)
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('90', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.36/0.56  thf('91', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.36/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['87', '90'])).
% 0.36/0.56  thf('92', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.36/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['91'])).
% 0.36/0.56  thf('93', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['2', '92'])).
% 0.36/0.56  thf('94', plain,
% 0.36/0.56      (![X19 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.36/0.56          | ~ (l1_struct_0 @ X19)
% 0.36/0.56          | (v2_struct_0 @ X19))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.56  thf('95', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['93', '94'])).
% 0.36/0.56  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.56  thf('97', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('demod', [status(thm)], ['95', '96'])).
% 0.36/0.56  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
