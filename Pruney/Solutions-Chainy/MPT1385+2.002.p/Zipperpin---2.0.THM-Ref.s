%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pPZEIc6PmW

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:58 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 419 expanded)
%              Number of leaves         :   30 ( 127 expanded)
%              Depth                    :   17
%              Number of atoms          : 1375 (6428 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( m1_connsp_2 @ ( sk_C @ X28 @ X27 ) @ X27 @ X28 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_connsp_2 @ X23 @ X21 @ X22 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_connsp_2 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
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

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m2_connsp_2 @ X20 @ X19 @ X18 )
      | ( r1_tarski @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('51',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('71',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('84',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ( m2_connsp_2 @ X20 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('95',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('96',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_connsp_2 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','116'])).

thf('118',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['70','117'])).

thf('119',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('120',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['70','117','119'])).

thf('121',plain,(
    v1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['69','118','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['29','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pPZEIc6PmW
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:16:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 213 iterations in 0.166s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.62  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.37/0.62  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.62  thf(t10_connsp_2, conjecture,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ( m2_connsp_2 @
% 0.37/0.62                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.37/0.62                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i]:
% 0.37/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.62            ( l1_pre_topc @ A ) ) =>
% 0.37/0.62          ( ![B:$i]:
% 0.37/0.62            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62              ( ![C:$i]:
% 0.37/0.62                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62                  ( ( m2_connsp_2 @
% 0.37/0.62                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.37/0.62                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.37/0.62  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(existence_m1_connsp_2, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.62         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (![X27 : $i, X28 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X27)
% 0.37/0.62          | ~ (v2_pre_topc @ X27)
% 0.37/0.62          | (v2_struct_0 @ X27)
% 0.37/0.62          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.37/0.62          | (m1_connsp_2 @ (sk_C @ X28 @ X27) @ X27 @ X28))),
% 0.37/0.62      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      (((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.62  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.37/0.62        | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.37/0.62  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('7', plain, ((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.37/0.62      inference('clc', [status(thm)], ['5', '6'])).
% 0.37/0.62  thf('8', plain, ((m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.37/0.62      inference('clc', [status(thm)], ['5', '6'])).
% 0.37/0.62  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_m1_connsp_2, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.62         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62       ( ![C:$i]:
% 0.37/0.62         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.37/0.62           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X21)
% 0.37/0.62          | ~ (v2_pre_topc @ X21)
% 0.37/0.62          | (v2_struct_0 @ X21)
% 0.37/0.62          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.37/0.62          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.62          | ~ (m1_connsp_2 @ X23 @ X21 @ X22))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.37/0.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.62  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 0.37/0.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62          | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.37/0.62  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 0.37/0.62      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['8', '16'])).
% 0.37/0.62  thf(t6_connsp_2, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.37/0.62          | ~ (m1_connsp_2 @ X29 @ X30 @ X31)
% 0.37/0.62          | (r2_hidden @ X31 @ X29)
% 0.37/0.62          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.37/0.62          | ~ (l1_pre_topc @ X30)
% 0.37/0.62          | ~ (v2_pre_topc @ X30)
% 0.37/0.62          | (v2_struct_0 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_A)
% 0.37/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r2_hidden @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.62          | ~ (m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ sk_A)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r2_hidden @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.62          | ~ (m1_connsp_2 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (((r2_hidden @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.37/0.62        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.62        | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['7', '22'])).
% 0.37/0.62  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (((r2_hidden @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('27', plain, ((r2_hidden @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.62      inference('clc', [status(thm)], ['25', '26'])).
% 0.37/0.62  thf(d1_xboole_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.62  thf('29', plain, (~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.62  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ X13)
% 0.37/0.62          | ~ (m1_subset_1 @ X14 @ X13)
% 0.37/0.62          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.37/0.62        | (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.62           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.62         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.37/0.62         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.62               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.62      inference('split', [status(esa)], ['33'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.62               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.62      inference('sup+', [status(thm)], ['32', '34'])).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t2_subset, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.62  thf('38', plain,
% 0.37/0.62      (![X11 : $i, X12 : $i]:
% 0.37/0.62         ((r2_hidden @ X11 @ X12)
% 0.37/0.62          | (v1_xboole_0 @ X12)
% 0.37/0.62          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.37/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.62  thf('39', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.62  thf(t63_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.62       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]:
% 0.37/0.62         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.37/0.62          | ~ (r2_hidden @ X7 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.37/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.62  thf(d2_connsp_2, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.37/0.62                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.62          | ~ (m2_connsp_2 @ X20 @ X19 @ X18)
% 0.37/0.62          | (r1_tarski @ X18 @ (k1_tops_1 @ X19 @ X20))
% 0.37/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.62          | ~ (l1_pre_topc @ X19)
% 0.37/0.62          | ~ (v2_pre_topc @ X19))),
% 0.37/0.62      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.37/0.62  thf('43', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.62          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.62  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('46', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.62          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.37/0.62      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.37/0.62  thf('47', plain,
% 0.37/0.62      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.62        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['36', '46'])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.37/0.63         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['35', '47'])).
% 0.37/0.63  thf('49', plain,
% 0.37/0.63      ((((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.63         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.63  thf(l1_zfmisc_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.63  thf('50', plain,
% 0.37/0.63      (![X4 : $i, X5 : $i]:
% 0.37/0.63         ((r2_hidden @ X4 @ X5) | ~ (r1_tarski @ (k1_tarski @ X4) @ X5))),
% 0.37/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.63  thf('51', plain,
% 0.37/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63         | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.37/0.63         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.63  thf('52', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(d1_connsp_2, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.63           ( ![C:$i]:
% 0.37/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.37/0.63                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.63  thf('53', plain,
% 0.37/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.37/0.63          | ~ (r2_hidden @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.37/0.63          | (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.37/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.63          | ~ (l1_pre_topc @ X16)
% 0.37/0.63          | ~ (v2_pre_topc @ X16)
% 0.37/0.63          | (v2_struct_0 @ X16))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.37/0.63  thf('54', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.63          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.37/0.63          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.63  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('57', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.37/0.63          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.37/0.63  thf('58', plain,
% 0.37/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.63         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.37/0.63         | (v2_struct_0 @ sk_A)))
% 0.37/0.63         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['51', '57'])).
% 0.37/0.63  thf('59', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('60', plain,
% 0.37/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.37/0.63         | (v2_struct_0 @ sk_A)))
% 0.37/0.63         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.37/0.63  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('62', plain,
% 0.37/0.63      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.37/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.63         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('clc', [status(thm)], ['60', '61'])).
% 0.37/0.63  thf('63', plain,
% 0.37/0.63      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.37/0.63        | ~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('64', plain,
% 0.37/0.63      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.37/0.63         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('split', [status(esa)], ['63'])).
% 0.37/0.63  thf('65', plain,
% 0.37/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 0.37/0.63             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['62', '64'])).
% 0.37/0.63  thf('66', plain,
% 0.37/0.63      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ 
% 0.37/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['8', '16'])).
% 0.37/0.63  thf(cc1_subset_1, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.37/0.63  thf('67', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.37/0.63          | (v1_xboole_0 @ X9)
% 0.37/0.63          | ~ (v1_xboole_0 @ X10))),
% 0.37/0.63      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.63  thf('68', plain,
% 0.37/0.63      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63        | (v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['66', '67'])).
% 0.37/0.63  thf('69', plain,
% 0.37/0.63      (((v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.37/0.63         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)) & 
% 0.37/0.63             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['65', '68'])).
% 0.37/0.63  thf('70', plain,
% 0.37/0.63      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)) | 
% 0.37/0.63       ~
% 0.37/0.63       ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.63      inference('split', [status(esa)], ['63'])).
% 0.37/0.63  thf('71', plain,
% 0.37/0.63      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.37/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('split', [status(esa)], ['33'])).
% 0.37/0.63  thf('72', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('73', plain,
% 0.37/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.37/0.63          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.37/0.63          | (r2_hidden @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.37/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.63          | ~ (l1_pre_topc @ X16)
% 0.37/0.63          | ~ (v2_pre_topc @ X16)
% 0.37/0.63          | (v2_struct_0 @ X16))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.37/0.63  thf('74', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.63          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.63          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.37/0.63  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('77', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.63          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.37/0.63  thf('78', plain,
% 0.37/0.63      (((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.63         | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.63         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['71', '77'])).
% 0.37/0.63  thf('79', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('80', plain,
% 0.37/0.63      ((((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.37/0.63         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('demod', [status(thm)], ['78', '79'])).
% 0.37/0.63  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('82', plain,
% 0.37/0.63      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.37/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('clc', [status(thm)], ['80', '81'])).
% 0.37/0.63  thf('83', plain,
% 0.37/0.63      (![X4 : $i, X6 : $i]:
% 0.37/0.63         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.37/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.63  thf('84', plain,
% 0.37/0.63      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.37/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.63  thf('85', plain,
% 0.37/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.37/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.63  thf('86', plain,
% 0.37/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.63          | ~ (r1_tarski @ X18 @ (k1_tops_1 @ X19 @ X20))
% 0.37/0.63          | (m2_connsp_2 @ X20 @ X19 @ X18)
% 0.37/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.63          | ~ (l1_pre_topc @ X19)
% 0.37/0.63          | ~ (v2_pre_topc @ X19))),
% 0.37/0.63      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.37/0.63  thf('87', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.63          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['85', '86'])).
% 0.37/0.63  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('90', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.63          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.37/0.63      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.37/0.63  thf('91', plain,
% 0.37/0.63      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.63         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['84', '90'])).
% 0.37/0.63  thf('92', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('93', plain,
% 0.37/0.63      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.63  thf('94', plain,
% 0.37/0.63      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.37/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.63  thf('95', plain,
% 0.37/0.63      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.37/0.63         <= (~
% 0.37/0.63             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('split', [status(esa)], ['63'])).
% 0.37/0.63  thf('96', plain,
% 0.37/0.63      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.63         <= (~
% 0.37/0.63             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['94', '95'])).
% 0.37/0.63  thf('97', plain,
% 0.37/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.63         <= (~
% 0.37/0.63             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.37/0.63             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['93', '96'])).
% 0.37/0.63  thf('98', plain,
% 0.37/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.63         <= (~
% 0.37/0.63             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.37/0.63             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['97'])).
% 0.37/0.63  thf('99', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('100', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.37/0.63          | (v1_xboole_0 @ X9)
% 0.37/0.63          | ~ (v1_xboole_0 @ X10))),
% 0.37/0.63      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.63  thf('101', plain,
% 0.37/0.63      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['99', '100'])).
% 0.37/0.63  thf('102', plain,
% 0.37/0.63      (((v1_xboole_0 @ sk_C_1))
% 0.37/0.63         <= (~
% 0.37/0.63             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.37/0.63             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['98', '101'])).
% 0.37/0.63  thf('103', plain,
% 0.37/0.63      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.37/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('split', [status(esa)], ['33'])).
% 0.37/0.63  thf('104', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('105', plain,
% 0.37/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('106', plain,
% 0.37/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.37/0.63          | ~ (m1_connsp_2 @ X29 @ X30 @ X31)
% 0.37/0.63          | (r2_hidden @ X31 @ X29)
% 0.37/0.63          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.37/0.63          | ~ (l1_pre_topc @ X30)
% 0.37/0.63          | ~ (v2_pre_topc @ X30)
% 0.37/0.63          | (v2_struct_0 @ X30))),
% 0.37/0.63      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.37/0.63  thf('107', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_hidden @ X0 @ sk_C_1)
% 0.37/0.63          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['105', '106'])).
% 0.37/0.63  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('110', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((v2_struct_0 @ sk_A)
% 0.37/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.63          | (r2_hidden @ X0 @ sk_C_1)
% 0.37/0.63          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.37/0.63      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.37/0.63  thf('111', plain,
% 0.37/0.63      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.37/0.63        | (r2_hidden @ sk_B_1 @ sk_C_1)
% 0.37/0.63        | (v2_struct_0 @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['104', '110'])).
% 0.37/0.63  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('113', plain,
% 0.37/0.63      (((r2_hidden @ sk_B_1 @ sk_C_1)
% 0.37/0.63        | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.37/0.63      inference('clc', [status(thm)], ['111', '112'])).
% 0.37/0.63  thf('114', plain,
% 0.37/0.63      (((r2_hidden @ sk_B_1 @ sk_C_1))
% 0.37/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['103', '113'])).
% 0.37/0.63  thf('115', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.63  thf('116', plain,
% 0.37/0.63      ((~ (v1_xboole_0 @ sk_C_1)) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['114', '115'])).
% 0.37/0.63  thf('117', plain,
% 0.37/0.63      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.37/0.63       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['102', '116'])).
% 0.37/0.63  thf('118', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.37/0.63      inference('sat_resolution*', [status(thm)], ['70', '117'])).
% 0.37/0.63  thf('119', plain,
% 0.37/0.63      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.37/0.63       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.37/0.63      inference('split', [status(esa)], ['33'])).
% 0.37/0.63  thf('120', plain,
% 0.37/0.63      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.37/0.63         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.37/0.63      inference('sat_resolution*', [status(thm)], ['70', '117', '119'])).
% 0.37/0.63  thf('121', plain, ((v1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.37/0.63      inference('simpl_trail', [status(thm)], ['69', '118', '120'])).
% 0.37/0.63  thf('122', plain, ($false), inference('demod', [status(thm)], ['29', '121'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
