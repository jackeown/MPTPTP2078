%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CS1oha62pO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 489 expanded)
%              Number of leaves         :   30 ( 145 expanded)
%              Depth                    :   20
%              Number of atoms          : 1441 (7718 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ( v2_struct_0 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( u1_struct_0 @ X54 ) )
      | ( m1_connsp_2 @ ( sk_C @ X55 @ X54 ) @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('3',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['6','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('11',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X48 ) )
      | ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( m1_connsp_2 @ X50 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

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

thf('19',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( m1_connsp_2 @ X56 @ X57 @ X58 )
      | ( r2_hidden @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ X57 ) )
      | ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ( v2_struct_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( ( k6_domain_1 @ X40 @ X41 )
        = ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('29',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ X38 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

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

thf('40',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( m2_connsp_2 @ X47 @ X46 @ X45 )
      | ( r1_tarski @ X45 @ ( k1_tops_1 @ X46 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( r2_hidden @ X42 @ ( k1_tops_1 @ X43 @ X44 ) )
      | ( m1_connsp_2 @ X44 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
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
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('67',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('71',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( m1_connsp_2 @ X56 @ X57 @ X58 )
      | ( r2_hidden @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ X57 ) )
      | ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ( v2_struct_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
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
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('84',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_connsp_2 @ X44 @ X43 @ X42 )
      | ( r2_hidden @ X42 @ ( k1_tops_1 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('96',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('100',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('102',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( r1_tarski @ X45 @ ( k1_tops_1 @ X46 @ X47 ) )
      | ( m2_connsp_2 @ X47 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('111',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('112',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['82','118'])).

thf('120',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['70','119'])).

thf('121',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('122',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['70','119','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['69','120','122'])).

thf('124',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['26','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['0','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CS1oha62pO
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 204 iterations in 0.067s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
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
% 0.21/0.53  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(existence_m1_connsp_2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X54 : $i, X55 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X54)
% 0.21/0.53          | ~ (v2_pre_topc @ X54)
% 0.21/0.53          | (v2_struct_0 @ X54)
% 0.21/0.53          | ~ (m1_subset_1 @ X55 @ (u1_struct_0 @ X54))
% 0.21/0.53          | (m1_connsp_2 @ (sk_C @ X55 @ X54) @ X54 @ X55))),
% 0.21/0.53      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.53  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('8', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m1_connsp_2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.21/0.53           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X48)
% 0.21/0.53          | ~ (v2_pre_topc @ X48)
% 0.21/0.53          | (v2_struct_0 @ X48)
% 0.21/0.53          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ X48))
% 0.21/0.53          | (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.21/0.53          | ~ (m1_connsp_2 @ X50 @ X48 @ X49))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.53  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '17'])).
% 0.21/0.53  thf(t6_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.21/0.53          | ~ (m1_connsp_2 @ X56 @ X57 @ X58)
% 0.21/0.53          | (r2_hidden @ X58 @ X56)
% 0.21/0.53          | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ X57))
% 0.21/0.53          | ~ (l1_pre_topc @ X57)
% 0.21/0.53          | ~ (v2_pre_topc @ X57)
% 0.21/0.53          | (v2_struct_0 @ X57))),
% 0.21/0.53      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.53          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.53          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '23'])).
% 0.21/0.53  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X40 : $i, X41 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ X40)
% 0.21/0.53          | ~ (m1_subset_1 @ X41 @ X40)
% 0.21/0.53          | ((k6_domain_1 @ X40 @ X41) = (k1_tarski @ X41)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.53        | (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['29', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_k6_domain_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X38 : $i, X39 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ X38)
% 0.21/0.53          | ~ (m1_subset_1 @ X39 @ X38)
% 0.21/0.53          | (m1_subset_1 @ (k6_domain_1 @ X38 @ X39) @ (k1_zfmisc_1 @ X38)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['34', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.53  thf(d2_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.21/0.53          | ~ (m2_connsp_2 @ X47 @ X46 @ X45)
% 0.21/0.53          | (r1_tarski @ X45 @ (k1_tops_1 @ X46 @ X47))
% 0.21/0.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.21/0.53          | ~ (l1_pre_topc @ X46)
% 0.21/0.53          | ~ (v2_pre_topc @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.53          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.53          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      ((((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('48', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf(t38_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.53         ((r2_hidden @ X28 @ X29)
% 0.21/0.53          | ~ (r1_tarski @ (k2_tarski @ X28 @ X30) @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d1_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.53                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X43))
% 0.21/0.53          | ~ (r2_hidden @ X42 @ (k1_tops_1 @ X43 @ X44))
% 0.21/0.53          | (m1_connsp_2 @ X44 @ X43 @ X42)
% 0.21/0.53          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.21/0.53          | ~ (l1_pre_topc @ X43)
% 0.21/0.53          | ~ (v2_pre_topc @ X43)
% 0.21/0.53          | (v2_struct_0 @ X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.53  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '57'])).
% 0.21/0.53  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.53  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.53        | ~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.21/0.53         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['63'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.21/0.53             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['62', '64'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '17'])).
% 0.21/0.53  thf(t5_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X35 @ X36)
% 0.21/0.53          | ~ (v1_xboole_0 @ X37)
% 0.21/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.53         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.21/0.53             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.21/0.53       ~
% 0.21/0.53       ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['63'])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.21/0.53          | ~ (m1_connsp_2 @ X56 @ X57 @ X58)
% 0.21/0.53          | (r2_hidden @ X58 @ X56)
% 0.21/0.53          | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ X57))
% 0.21/0.53          | ~ (l1_pre_topc @ X57)
% 0.21/0.53          | ~ (v2_pre_topc @ X57)
% 0.21/0.53          | (v2_struct_0 @ X57))),
% 0.21/0.53      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.53          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.53  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('78', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.53          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.21/0.53        | (r2_hidden @ sk_B @ sk_C_1)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['72', '78'])).
% 0.21/0.53  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ sk_C_1) | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.21/0.53      inference('clc', [status(thm)], ['79', '80'])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ sk_C_1))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['71', '81'])).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X43))
% 0.21/0.53          | ~ (m1_connsp_2 @ X44 @ X43 @ X42)
% 0.21/0.53          | (r2_hidden @ X42 @ (k1_tops_1 @ X43 @ X44))
% 0.21/0.53          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.21/0.53          | ~ (l1_pre_topc @ X43)
% 0.21/0.53          | ~ (v2_pre_topc @ X43)
% 0.21/0.53          | (v2_struct_0 @ X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.53  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('89', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['83', '89'])).
% 0.21/0.53  thf('91', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('92', plain,
% 0.21/0.53      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.53  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('clc', [status(thm)], ['92', '93'])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('clc', [status(thm)], ['92', '93'])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_tarski @ X28 @ X30) @ X31)
% 0.21/0.53          | ~ (r2_hidden @ X30 @ X31)
% 0.21/0.53          | ~ (r2_hidden @ X28 @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.53  thf('97', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.21/0.53           | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.53  thf('98', plain,
% 0.21/0.53      (((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['94', '97'])).
% 0.21/0.53  thf('99', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf('100', plain,
% 0.21/0.53      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.53  thf('101', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.53  thf('102', plain,
% 0.21/0.53      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.21/0.53          | ~ (r1_tarski @ X45 @ (k1_tops_1 @ X46 @ X47))
% 0.21/0.53          | (m2_connsp_2 @ X47 @ X46 @ X45)
% 0.21/0.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.21/0.53          | ~ (l1_pre_topc @ X46)
% 0.21/0.53          | ~ (v2_pre_topc @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.53          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.53  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('106', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.53          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.21/0.53  thf('107', plain,
% 0.21/0.53      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.53         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['100', '106'])).
% 0.21/0.53  thf('108', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('109', plain,
% 0.21/0.53      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['107', '108'])).
% 0.21/0.53  thf('110', plain,
% 0.21/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('111', plain,
% 0.21/0.53      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['63'])).
% 0.21/0.53  thf('112', plain,
% 0.21/0.53      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (~
% 0.21/0.53             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.53  thf('113', plain,
% 0.21/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53         <= (~
% 0.21/0.53             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.21/0.53             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['109', '112'])).
% 0.21/0.53  thf('114', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.21/0.53             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['113'])).
% 0.21/0.53  thf('115', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('116', plain,
% 0.21/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X35 @ X36)
% 0.21/0.53          | ~ (v1_xboole_0 @ X37)
% 0.21/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.53  thf('117', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['115', '116'])).
% 0.21/0.53  thf('118', plain,
% 0.21/0.53      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 0.21/0.53         <= (~
% 0.21/0.53             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.21/0.53             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['114', '117'])).
% 0.21/0.53  thf('119', plain,
% 0.21/0.53      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.21/0.53       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['82', '118'])).
% 0.21/0.53  thf('120', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['70', '119'])).
% 0.21/0.53  thf('121', plain,
% 0.21/0.53      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.21/0.53       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.21/0.53      inference('split', [status(esa)], ['30'])).
% 0.21/0.53  thf('122', plain,
% 0.21/0.53      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.21/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['70', '119', '121'])).
% 0.21/0.53  thf('123', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['69', '120', '122'])).
% 0.21/0.53  thf('124', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('clc', [status(thm)], ['26', '123'])).
% 0.21/0.53  thf('125', plain, ($false), inference('demod', [status(thm)], ['0', '124'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
