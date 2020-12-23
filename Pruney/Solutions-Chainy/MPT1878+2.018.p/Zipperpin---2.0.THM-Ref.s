%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bwFr7sDEZX

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:05 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 138 expanded)
%              Number of leaves         :   37 (  57 expanded)
%              Depth                    :   23
%              Number of atoms          :  607 (1067 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(t46_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( v3_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v2_tex_2 @ X27 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( X25 = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ ( sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ ( sk_B_2 @ sk_A ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( sk_B_2 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_xboole_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ ( sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_2 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bwFr7sDEZX
% 0.16/0.36  % Computer   : n018.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 20:13:57 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 913 iterations in 0.453s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.89  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.70/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.89  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.70/0.89  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.70/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.70/0.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.70/0.89  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.70/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.70/0.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.70/0.89  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.70/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.70/0.89  thf(t46_tex_2, conjecture,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( ( v1_xboole_0 @ B ) & 
% 0.70/0.89             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.70/0.89           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i]:
% 0.70/0.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.70/0.89            ( l1_pre_topc @ A ) ) =>
% 0.70/0.89          ( ![B:$i]:
% 0.70/0.89            ( ( ( v1_xboole_0 @ B ) & 
% 0.70/0.89                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.70/0.89              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.70/0.89  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(d1_xboole_0, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('2', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('3', plain, ((v1_xboole_0 @ sk_B_3)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(l13_xboole_0, axiom,
% 0.70/0.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.70/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.89  thf('5', plain, (((sk_B_3) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.89  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '5'])).
% 0.70/0.89  thf(existence_m1_subset_1, axiom,
% 0.70/0.89    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.70/0.89  thf('7', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 0.70/0.89      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.70/0.89  thf(redefinition_k6_domain_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.70/0.89       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ X22)
% 0.70/0.89          | ~ (m1_subset_1 @ X23 @ X22)
% 0.70/0.89          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.70/0.89          | (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('10', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 0.70/0.89      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.70/0.89  thf(t36_tex_2, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.70/0.89           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X28 : $i, X29 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.70/0.89          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.70/0.89          | ~ (l1_pre_topc @ X29)
% 0.70/0.89          | ~ (v2_pre_topc @ X29)
% 0.70/0.89          | (v2_struct_0 @ X29))),
% 0.70/0.89      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X0)
% 0.70/0.89          | ~ (v2_pre_topc @ X0)
% 0.70/0.89          | ~ (l1_pre_topc @ X0)
% 0.70/0.89          | (v2_tex_2 @ 
% 0.70/0.89             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B_1 @ (u1_struct_0 @ X0))) @ 
% 0.70/0.89             X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.70/0.89          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (l1_pre_topc @ X0)
% 0.70/0.89          | ~ (v2_pre_topc @ X0)
% 0.70/0.89          | (v2_struct_0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['9', '12'])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.70/0.89          | (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('15', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 0.70/0.89      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.70/0.89  thf(dt_k6_domain_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.70/0.89       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (![X20 : $i, X21 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ X20)
% 0.70/0.89          | ~ (m1_subset_1 @ X21 @ X20)
% 0.70/0.89          | (m1_subset_1 @ (k6_domain_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20)))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B_1 @ X0)) @ 
% 0.70/0.89           (k1_zfmisc_1 @ X0))
% 0.70/0.89          | (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((m1_subset_1 @ (k1_tarski @ (sk_B_1 @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.70/0.89          | (v1_xboole_0 @ X0)
% 0.70/0.89          | (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['14', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ X0)
% 0.70/0.89          | (m1_subset_1 @ (k1_tarski @ (sk_B_1 @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['18'])).
% 0.70/0.89  thf(t4_subset_1, axiom,
% 0.70/0.89    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.70/0.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.89  thf(d7_tex_2, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_pre_topc @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89           ( ( v3_tex_2 @ B @ A ) <=>
% 0.70/0.89             ( ( v2_tex_2 @ B @ A ) & 
% 0.70/0.89               ( ![C:$i]:
% 0.70/0.89                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.70/0.89                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.70/0.89          | ~ (v3_tex_2 @ X25 @ X26)
% 0.70/0.89          | ~ (v2_tex_2 @ X27 @ X26)
% 0.70/0.89          | ~ (r1_tarski @ X25 @ X27)
% 0.70/0.89          | ((X25) = (X27))
% 0.70/0.89          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.70/0.89          | ~ (l1_pre_topc @ X26))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (l1_pre_topc @ X0)
% 0.70/0.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.70/0.89          | ((k1_xboole_0) = (X1))
% 0.70/0.89          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.70/0.89          | ~ (v2_tex_2 @ X1 @ X0)
% 0.70/0.89          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.89  thf('23', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.70/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (l1_pre_topc @ X0)
% 0.70/0.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.70/0.89          | ((k1_xboole_0) = (X1))
% 0.70/0.89          | ~ (v2_tex_2 @ X1 @ X0)
% 0.70/0.89          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['22', '23'])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.89          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.70/0.89          | ((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))))
% 0.70/0.89          | ~ (l1_pre_topc @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['19', '24'])).
% 0.70/0.89  thf(t1_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.89  thf('26', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.70/0.89  thf(t49_zfmisc_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X10 : $i, X11 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ (k1_tarski @ X10) @ X11) != (k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.70/0.89  thf('28', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.89          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.70/0.89          | ~ (l1_pre_topc @ X0))),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v2_struct_0 @ X0)
% 0.70/0.89          | ~ (v2_pre_topc @ X0)
% 0.70/0.89          | ~ (l1_pre_topc @ X0)
% 0.70/0.89          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (l1_pre_topc @ X0)
% 0.70/0.89          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.89          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['13', '29'])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.70/0.89          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (l1_pre_topc @ X0)
% 0.70/0.89          | ~ (v2_pre_topc @ X0)
% 0.70/0.89          | (v2_struct_0 @ X0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['30'])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (((v2_struct_0 @ sk_A)
% 0.70/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.70/0.89        | ~ (l1_pre_topc @ sk_A)
% 0.70/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['6', '31'])).
% 0.70/0.89  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.89      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.70/0.89  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('37', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.70/0.89      inference('clc', [status(thm)], ['35', '36'])).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.70/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.89  thf('39', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.70/0.89  thf(rc3_tops_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.89       ( ?[B:$i]:
% 0.70/0.89         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.70/0.89           ( ~( v1_xboole_0 @ B ) ) & 
% 0.70/0.89           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (![X24 : $i]:
% 0.70/0.89         ((m1_subset_1 @ (sk_B_2 @ X24) @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.70/0.89          | ~ (l1_pre_topc @ X24)
% 0.70/0.89          | ~ (v2_pre_topc @ X24)
% 0.70/0.89          | (v2_struct_0 @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      (((m1_subset_1 @ (sk_B_2 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.70/0.89        | (v2_struct_0 @ sk_A)
% 0.70/0.89        | ~ (v2_pre_topc @ sk_A)
% 0.70/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.89      inference('sup+', [status(thm)], ['39', '40'])).
% 0.70/0.89  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      (((m1_subset_1 @ (sk_B_2 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.70/0.89        | (v2_struct_0 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.70/0.89  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      ((m1_subset_1 @ (sk_B_2 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.70/0.89      inference('clc', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf(t3_subset, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X14 : $i, X15 : $i]:
% 0.70/0.89         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.89  thf('48', plain, ((r1_tarski @ (sk_B_2 @ sk_A) @ k1_xboole_0)),
% 0.70/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.70/0.89  thf(d3_tarski, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X3 @ X4)
% 0.70/0.89          | (r2_hidden @ X3 @ X5)
% 0.70/0.89          | ~ (r1_tarski @ X4 @ X5))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ (sk_B_2 @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['48', '49'])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      (((v1_xboole_0 @ (sk_B_2 @ sk_A))
% 0.70/0.89        | (r2_hidden @ (sk_B @ (sk_B_2 @ sk_A)) @ k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '50'])).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('53', plain,
% 0.70/0.89      (((v1_xboole_0 @ (sk_B_2 @ sk_A)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.70/0.89  thf('54', plain, ((v1_xboole_0 @ sk_B_3)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('55', plain, (((sk_B_3) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.89  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('demod', [status(thm)], ['54', '55'])).
% 0.70/0.89  thf('57', plain, ((v1_xboole_0 @ (sk_B_2 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['53', '56'])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (![X24 : $i]:
% 0.70/0.89         (~ (v1_xboole_0 @ (sk_B_2 @ X24))
% 0.70/0.89          | ~ (l1_pre_topc @ X24)
% 0.70/0.89          | ~ (v2_pre_topc @ X24)
% 0.70/0.89          | (v2_struct_0 @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['57', '58'])).
% 0.70/0.89  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.70/0.89      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.70/0.89  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
