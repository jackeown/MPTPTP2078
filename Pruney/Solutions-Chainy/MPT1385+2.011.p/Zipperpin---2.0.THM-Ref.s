%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6dvU2HZ8M

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 436 expanded)
%              Number of leaves         :   32 ( 133 expanded)
%              Depth                    :   33
%              Number of atoms          : 1119 (6244 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m2_connsp_2 @ X31 @ X30 @ X29 )
      | ( r1_tarski @ X29 @ ( k1_tops_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( ( k6_domain_1 @ X24 @ X25 )
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('20',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_connsp_2 @ X28 @ X27 @ X26 )
      | ( r2_hidden @ X26 @ ( k1_tops_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( r1_tarski @ X29 @ ( k1_tops_1 @ X30 @ X31 ) )
      | ( m2_connsp_2 @ X31 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('52',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('53',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('56',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('57',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('65',plain,(
    m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['25','63','64'])).

thf('66',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['23','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['17','66'])).

thf('68',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','71'])).

thf('73',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ ( k1_tops_1 @ X27 @ X28 ) )
      | ( m1_connsp_2 @ X28 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('85',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['25','63'])).

thf('86',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','94'])).

thf('96',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('99',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6dvU2HZ8M
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:20:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 250 iterations in 0.103s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(t10_connsp_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( m2_connsp_2 @
% 0.21/0.53                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.21/0.53                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                  ( ( m2_connsp_2 @
% 0.21/0.53                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.21/0.53                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('1', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf(d2_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (((X1) != (X0))
% 0.21/0.53          | (r2_hidden @ X1 @ X2)
% 0.21/0.53          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.54  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['1', '3'])).
% 0.21/0.54  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['1', '3'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t2_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((r2_hidden @ X9 @ X10)
% 0.21/0.54          | (v1_xboole_0 @ X10)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf(t63_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.21/0.54          | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf(d2_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.54          | ~ (m2_connsp_2 @ X31 @ X30 @ X29)
% 0.21/0.54          | (r1_tarski @ X29 @ (k1_tops_1 @ X30 @ X31))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.54          | ~ (l1_pre_topc @ X30)
% 0.21/0.54          | ~ (v2_pre_topc @ X30))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.54          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.54          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '16'])).
% 0.21/0.54  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X24)
% 0.21/0.54          | ~ (m1_subset_1 @ X25 @ X24)
% 0.21/0.54          | ((k6_domain_1 @ X24 @ X25) = (k1_tarski @ X25)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.54         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['20', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | ~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.21/0.54       ~
% 0.21/0.54       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['21'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d1_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.21/0.54          | ~ (m1_connsp_2 @ X28 @ X27 @ X26)
% 0.21/0.54          | (r2_hidden @ X26 @ (k1_tops_1 @ X27 @ X28))
% 0.21/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.54          | ~ (l1_pre_topc @ X27)
% 0.21/0.54          | ~ (v2_pre_topc @ X27)
% 0.21/0.54          | (v2_struct_0 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '32'])).
% 0.21/0.54  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.21/0.54          | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.54          | ~ (r1_tarski @ X29 @ (k1_tops_1 @ X30 @ X31))
% 0.21/0.54          | (m2_connsp_2 @ X31 @ X30 @ X29)
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.54          | ~ (l1_pre_topc @ X30)
% 0.21/0.54          | ~ (v2_pre_topc @ X30))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['24'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.21/0.54             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.21/0.54             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.54  thf(fc2_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X21 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.21/0.54          | ~ (l1_struct_0 @ X21)
% 0.21/0.54          | (v2_struct_0 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.21/0.54             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.21/0.54             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['57', '60'])).
% 0.21/0.54  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.21/0.54       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.21/0.54       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['21'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.21/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['25', '63', '64'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['23', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.21/0.54      inference('clc', [status(thm)], ['17', '66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (![X11 : $i, X13 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf(t4_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X14 @ X15)
% 0.21/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.21/0.54          | (m1_subset_1 @ X14 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (m1_subset_1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '71'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((r2_hidden @ X9 @ X10)
% 0.21/0.54          | (v1_xboole_0 @ X10)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.21/0.54          | ~ (r2_hidden @ X26 @ (k1_tops_1 @ X27 @ X28))
% 0.21/0.54          | (m1_connsp_2 @ X28 @ X27 @ X26)
% 0.21/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.54          | ~ (l1_pre_topc @ X27)
% 0.21/0.54          | ~ (v2_pre_topc @ X27)
% 0.21/0.54          | (v2_struct_0 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.54  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['74', '80'])).
% 0.21/0.54  thf('82', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['24'])).
% 0.21/0.54  thf('85', plain, (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['25', '63'])).
% 0.21/0.54  thf('86', plain, (~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['84', '85'])).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['83', '86'])).
% 0.21/0.54  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('89', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf(t5_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X17 @ X18)
% 0.21/0.54          | ~ (v1_xboole_0 @ X19)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.21/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['89', '92'])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.21/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['93'])).
% 0.21/0.54  thf('95', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '94'])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (![X21 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.21/0.54          | ~ (l1_struct_0 @ X21)
% 0.21/0.54          | (v2_struct_0 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.54  thf('97', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.54  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('99', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['97', '98'])).
% 0.21/0.54  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
