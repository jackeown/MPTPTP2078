%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4l9QInOFwt

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:58 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 434 expanded)
%              Number of leaves         :   29 ( 130 expanded)
%              Depth                    :   18
%              Number of atoms          : 1391 (6710 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( m1_connsp_2 @ ( sk_C @ X26 @ X25 ) @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('2',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_connsp_2 @ X21 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_connsp_2 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('32',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

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

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m2_connsp_2 @ X18 @ X17 @ X16 )
      | ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('52',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['64'])).

thf('72',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('87',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ( m2_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('96',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['64'])).

thf('97',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('102',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_connsp_2 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['103','117'])).

thf('119',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['71','118'])).

thf('120',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('121',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['71','118','120'])).

thf('122',plain,(
    v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','119','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['29','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4l9QInOFwt
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 167 iterations in 0.102s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.36/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
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
% 0.36/0.56  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(existence_m1_connsp_2, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X25 : $i, X26 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X25)
% 0.36/0.56          | ~ (v2_pre_topc @ X25)
% 0.36/0.56          | (v2_struct_0 @ X25)
% 0.36/0.56          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.36/0.56          | (m1_connsp_2 @ (sk_C @ X26 @ X25) @ X25 @ X26))),
% 0.36/0.56      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.36/0.56        | (v2_struct_0 @ sk_A)
% 0.36/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.56  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.36/0.56        | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.56  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('7', plain, ((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.36/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf('8', plain, ((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.36/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(dt_m1_connsp_2, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56       ( ![C:$i]:
% 0.36/0.56         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.36/0.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X19)
% 0.36/0.56          | ~ (v2_pre_topc @ X19)
% 0.36/0.56          | (v2_struct_0 @ X19)
% 0.36/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.36/0.56          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.56          | ~ (m1_connsp_2 @ X21 @ X19 @ X20))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.36/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.56  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.36/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.36/0.56  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('clc', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.36/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '16'])).
% 0.36/0.56  thf(t6_connsp_2, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.56               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.56          | ~ (m1_connsp_2 @ X27 @ X28 @ X29)
% 0.36/0.56          | (r2_hidden @ X29 @ X27)
% 0.36/0.56          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.36/0.56          | ~ (l1_pre_topc @ X28)
% 0.36/0.56          | ~ (v2_pre_topc @ X28)
% 0.36/0.56          | (v2_struct_0 @ X28))),
% 0.36/0.56      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | (r2_hidden @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.56  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | (r2_hidden @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.56          | ~ (m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (((r2_hidden @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.56        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '22'])).
% 0.36/0.56  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (((r2_hidden @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.56  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('27', plain, ((r2_hidden @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.56      inference('clc', [status(thm)], ['25', '26'])).
% 0.36/0.56  thf(d1_xboole_0, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.56  thf('29', plain, (~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.56  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X11 : $i, X12 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ X11)
% 0.36/0.56          | ~ (m1_subset_1 @ X12 @ X11)
% 0.36/0.56          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.56        | (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('split', [status(esa)], ['33'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('sup+', [status(thm)], ['32', '34'])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.56  thf('38', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(dt_k6_domain_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.56       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (![X9 : $i, X10 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ X9)
% 0.36/0.56          | ~ (m1_subset_1 @ X10 @ X9)
% 0.36/0.56          | (m1_subset_1 @ (k6_domain_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.36/0.56      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.36/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.36/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['37', '40'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.36/0.56  thf(d2_connsp_2, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.56                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.56          | ~ (m2_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.56          | (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.36/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.56          | ~ (l1_pre_topc @ X17)
% 0.36/0.56          | ~ (v2_pre_topc @ X17))),
% 0.36/0.56      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.56  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.36/0.56      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.56        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['36', '47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['35', '48'])).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      ((((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.56  thf(l1_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (![X4 : $i, X5 : $i]:
% 0.36/0.56         ((r2_hidden @ X4 @ X5) | ~ (r1_tarski @ (k1_tarski @ X4) @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.56  thf('53', plain,
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
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.36/0.56          | ~ (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.36/0.56          | (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.36/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.56          | ~ (l1_pre_topc @ X14)
% 0.36/0.56          | ~ (v2_pre_topc @ X14)
% 0.36/0.56          | (v2_struct_0 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.56  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['52', '58'])).
% 0.36/0.56  thf('60', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.56         | (v2_struct_0 @ sk_A)))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.56  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('clc', [status(thm)], ['61', '62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.56        | ~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.36/0.56         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['64'])).
% 0.36/0.56  thf('66', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['63', '65'])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.36/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '16'])).
% 0.36/0.56  thf(cc1_subset_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.36/0.56          | (v1_xboole_0 @ X7)
% 0.36/0.56          | ~ (v1_xboole_0 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      (((v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.36/0.56         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['66', '69'])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)) | 
% 0.36/0.56       ~
% 0.36/0.56       ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['64'])).
% 0.36/0.56  thf('72', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['33'])).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.36/0.56          | ~ (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.36/0.56          | (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.36/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.56          | ~ (l1_pre_topc @ X14)
% 0.36/0.56          | ~ (v2_pre_topc @ X14)
% 0.36/0.56          | (v2_struct_0 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.56  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('78', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.36/0.56  thf('79', plain,
% 0.36/0.56      (((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['72', '78'])).
% 0.36/0.56  thf('80', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      ((((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.56  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('83', plain,
% 0.36/0.56      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('clc', [status(thm)], ['81', '82'])).
% 0.36/0.56  thf('84', plain,
% 0.36/0.56      (![X4 : $i, X6 : $i]:
% 0.36/0.56         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.36/0.56  thf('86', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.36/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.36/0.56  thf('87', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.56          | ~ (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.36/0.56          | (m2_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.56          | ~ (l1_pre_topc @ X17)
% 0.36/0.56          | ~ (v2_pre_topc @ X17))),
% 0.36/0.56      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.36/0.56  thf('88', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.56          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.36/0.56  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('91', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.56          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.36/0.56  thf('92', plain,
% 0.36/0.56      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.56         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['85', '91'])).
% 0.36/0.56  thf('93', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('94', plain,
% 0.36/0.56      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('demod', [status(thm)], ['92', '93'])).
% 0.36/0.56  thf('95', plain,
% 0.36/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.36/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.56  thf('96', plain,
% 0.36/0.56      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('split', [status(esa)], ['64'])).
% 0.36/0.56  thf('97', plain,
% 0.36/0.56      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.56  thf('98', plain,
% 0.36/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.36/0.56             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['94', '97'])).
% 0.36/0.56  thf('99', plain,
% 0.36/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.36/0.56             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['98'])).
% 0.36/0.56  thf('100', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('101', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.36/0.56          | (v1_xboole_0 @ X7)
% 0.36/0.56          | ~ (v1_xboole_0 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.56  thf('102', plain,
% 0.36/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['100', '101'])).
% 0.36/0.56  thf('103', plain,
% 0.36/0.56      (((v1_xboole_0 @ sk_C_1))
% 0.36/0.56         <= (~
% 0.36/0.56             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.36/0.56             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['99', '102'])).
% 0.36/0.56  thf('104', plain,
% 0.36/0.56      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['33'])).
% 0.36/0.56  thf('105', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('106', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('107', plain,
% 0.36/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.56          | ~ (m1_connsp_2 @ X27 @ X28 @ X29)
% 0.36/0.56          | (r2_hidden @ X29 @ X27)
% 0.36/0.56          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.36/0.56          | ~ (l1_pre_topc @ X28)
% 0.36/0.56          | ~ (v2_pre_topc @ X28)
% 0.36/0.56          | (v2_struct_0 @ X28))),
% 0.36/0.56      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.36/0.56  thf('108', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | (r2_hidden @ X0 @ sk_C_1)
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['106', '107'])).
% 0.36/0.56  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('111', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((v2_struct_0 @ sk_A)
% 0.36/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.56          | (r2_hidden @ X0 @ sk_C_1)
% 0.36/0.56          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.36/0.56  thf('112', plain,
% 0.36/0.56      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.56        | (r2_hidden @ sk_B_1 @ sk_C_1)
% 0.36/0.56        | (v2_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['105', '111'])).
% 0.36/0.56  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('114', plain,
% 0.36/0.56      (((r2_hidden @ sk_B_1 @ sk_C_1)
% 0.36/0.56        | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('clc', [status(thm)], ['112', '113'])).
% 0.36/0.56  thf('115', plain,
% 0.36/0.56      (((r2_hidden @ sk_B_1 @ sk_C_1))
% 0.36/0.56         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['104', '114'])).
% 0.36/0.56  thf('116', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.56  thf('117', plain,
% 0.36/0.56      ((~ (v1_xboole_0 @ sk_C_1)) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['115', '116'])).
% 0.36/0.56  thf('118', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.36/0.56       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['103', '117'])).
% 0.36/0.56  thf('119', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['71', '118'])).
% 0.36/0.56  thf('120', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.36/0.56       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('split', [status(esa)], ['33'])).
% 0.36/0.56  thf('121', plain,
% 0.36/0.56      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.36/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['71', '118', '120'])).
% 0.36/0.56  thf('122', plain, ((v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['70', '119', '121'])).
% 0.36/0.56  thf('123', plain, ($false), inference('demod', [status(thm)], ['29', '122'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
