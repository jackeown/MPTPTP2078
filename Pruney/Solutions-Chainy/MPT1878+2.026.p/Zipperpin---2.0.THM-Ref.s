%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LvDLrdOGr

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:06 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 135 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  581 (1028 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
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

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_tex_2 @ X23 @ X24 )
      | ~ ( v2_tex_2 @ X25 @ X24 )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( X23 = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','39'])).

thf('41',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('52',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LvDLrdOGr
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.40/1.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.40/1.58  % Solved by: fo/fo7.sh
% 1.40/1.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.40/1.58  % done 856 iterations in 1.130s
% 1.40/1.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.40/1.58  % SZS output start Refutation
% 1.40/1.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.40/1.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.40/1.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.40/1.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.40/1.58  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.40/1.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.40/1.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.40/1.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.40/1.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.40/1.58  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.40/1.58  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.40/1.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.40/1.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.40/1.58  thf(sk_B_type, type, sk_B: $i > $i).
% 1.40/1.58  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.40/1.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.40/1.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.40/1.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.40/1.58  thf(sk_A_type, type, sk_A: $i).
% 1.40/1.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.40/1.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.40/1.58  thf(t46_tex_2, conjecture,
% 1.40/1.58    (![A:$i]:
% 1.40/1.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.40/1.58       ( ![B:$i]:
% 1.40/1.58         ( ( ( v1_xboole_0 @ B ) & 
% 1.40/1.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.40/1.58           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.40/1.58  thf(zf_stmt_0, negated_conjecture,
% 1.40/1.58    (~( ![A:$i]:
% 1.40/1.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.40/1.58            ( l1_pre_topc @ A ) ) =>
% 1.40/1.58          ( ![B:$i]:
% 1.40/1.58            ( ( ( v1_xboole_0 @ B ) & 
% 1.40/1.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.40/1.58              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 1.40/1.58    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 1.40/1.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf(t29_mcart_1, axiom,
% 1.40/1.58    (![A:$i]:
% 1.40/1.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.40/1.58          ( ![B:$i]:
% 1.40/1.58            ( ~( ( r2_hidden @ B @ A ) & 
% 1.40/1.58                 ( ![C:$i,D:$i,E:$i]:
% 1.40/1.58                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.40/1.58                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 1.40/1.58  thf('1', plain,
% 1.40/1.58      (![X13 : $i]:
% 1.40/1.58         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 1.40/1.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 1.40/1.58  thf(d1_xboole_0, axiom,
% 1.40/1.58    (![A:$i]:
% 1.40/1.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.40/1.58  thf('2', plain,
% 1.40/1.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.40/1.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.40/1.58  thf('3', plain,
% 1.40/1.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['1', '2'])).
% 1.40/1.58  thf('4', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf('5', plain, ((v1_xboole_0 @ sk_B_2)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf('6', plain,
% 1.40/1.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['1', '2'])).
% 1.40/1.58  thf('7', plain, (((sk_B_2) = (k1_xboole_0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['5', '6'])).
% 1.40/1.58  thf('8', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.40/1.58      inference('demod', [status(thm)], ['4', '7'])).
% 1.40/1.58  thf('9', plain,
% 1.40/1.58      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('sup+', [status(thm)], ['3', '8'])).
% 1.40/1.58  thf('10', plain,
% 1.40/1.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.40/1.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.40/1.58  thf(t1_subset, axiom,
% 1.40/1.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.40/1.58  thf('11', plain,
% 1.40/1.58      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 1.40/1.58      inference('cnf', [status(esa)], [t1_subset])).
% 1.40/1.58  thf('12', plain,
% 1.40/1.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['10', '11'])).
% 1.40/1.58  thf(redefinition_k6_domain_1, axiom,
% 1.40/1.58    (![A:$i,B:$i]:
% 1.40/1.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.40/1.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.40/1.58  thf('13', plain,
% 1.40/1.58      (![X21 : $i, X22 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ X21)
% 1.40/1.58          | ~ (m1_subset_1 @ X22 @ X21)
% 1.40/1.58          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 1.40/1.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.40/1.58  thf('14', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ X0)
% 1.40/1.58          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.40/1.58          | (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['12', '13'])).
% 1.40/1.58  thf('15', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.40/1.58          | (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('simplify', [status(thm)], ['14'])).
% 1.40/1.58  thf('16', plain,
% 1.40/1.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['10', '11'])).
% 1.40/1.58  thf(t36_tex_2, axiom,
% 1.40/1.58    (![A:$i]:
% 1.40/1.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.40/1.58       ( ![B:$i]:
% 1.40/1.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.40/1.58           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.40/1.58  thf('17', plain,
% 1.40/1.58      (![X26 : $i, X27 : $i]:
% 1.40/1.58         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 1.40/1.58          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 1.40/1.58          | ~ (l1_pre_topc @ X27)
% 1.40/1.58          | ~ (v2_pre_topc @ X27)
% 1.40/1.58          | (v2_struct_0 @ X27))),
% 1.40/1.58      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.40/1.58  thf('18', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.40/1.58          | (v2_struct_0 @ X0)
% 1.40/1.58          | ~ (v2_pre_topc @ X0)
% 1.40/1.58          | ~ (l1_pre_topc @ X0)
% 1.40/1.58          | (v2_tex_2 @ 
% 1.40/1.58             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 1.40/1.58             X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['16', '17'])).
% 1.40/1.58  thf('19', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.40/1.58          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.40/1.58          | ~ (l1_pre_topc @ X0)
% 1.40/1.58          | ~ (v2_pre_topc @ X0)
% 1.40/1.58          | (v2_struct_0 @ X0)
% 1.40/1.58          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.40/1.58      inference('sup+', [status(thm)], ['15', '18'])).
% 1.40/1.58  thf('20', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v2_struct_0 @ X0)
% 1.40/1.58          | ~ (v2_pre_topc @ X0)
% 1.40/1.58          | ~ (l1_pre_topc @ X0)
% 1.40/1.58          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.40/1.58          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 1.40/1.58      inference('simplify', [status(thm)], ['19'])).
% 1.40/1.58  thf('21', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.40/1.58          | (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('simplify', [status(thm)], ['14'])).
% 1.40/1.58  thf('22', plain,
% 1.40/1.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['10', '11'])).
% 1.40/1.58  thf(dt_k6_domain_1, axiom,
% 1.40/1.58    (![A:$i,B:$i]:
% 1.40/1.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.40/1.58       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.40/1.58  thf('23', plain,
% 1.40/1.58      (![X19 : $i, X20 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ X19)
% 1.40/1.58          | ~ (m1_subset_1 @ X20 @ X19)
% 1.40/1.58          | (m1_subset_1 @ (k6_domain_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19)))),
% 1.40/1.58      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.40/1.58  thf('24', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ X0)
% 1.40/1.58          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 1.40/1.58             (k1_zfmisc_1 @ X0))
% 1.40/1.58          | (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['22', '23'])).
% 1.40/1.58  thf('25', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.40/1.58          | (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('simplify', [status(thm)], ['24'])).
% 1.40/1.58  thf('26', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.40/1.58          | (v1_xboole_0 @ X0)
% 1.40/1.58          | (v1_xboole_0 @ X0))),
% 1.40/1.58      inference('sup+', [status(thm)], ['21', '25'])).
% 1.40/1.58  thf('27', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ X0)
% 1.40/1.58          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 1.40/1.58      inference('simplify', [status(thm)], ['26'])).
% 1.40/1.58  thf(t4_subset_1, axiom,
% 1.40/1.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.40/1.58  thf('28', plain,
% 1.40/1.58      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.40/1.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.40/1.58  thf(d7_tex_2, axiom,
% 1.40/1.58    (![A:$i]:
% 1.40/1.58     ( ( l1_pre_topc @ A ) =>
% 1.40/1.58       ( ![B:$i]:
% 1.40/1.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.40/1.58           ( ( v3_tex_2 @ B @ A ) <=>
% 1.40/1.58             ( ( v2_tex_2 @ B @ A ) & 
% 1.40/1.58               ( ![C:$i]:
% 1.40/1.58                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.40/1.58                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.40/1.58                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.40/1.58  thf('29', plain,
% 1.40/1.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.40/1.58         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.40/1.58          | ~ (v3_tex_2 @ X23 @ X24)
% 1.40/1.58          | ~ (v2_tex_2 @ X25 @ X24)
% 1.40/1.58          | ~ (r1_tarski @ X23 @ X25)
% 1.40/1.58          | ((X23) = (X25))
% 1.40/1.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.40/1.58          | ~ (l1_pre_topc @ X24))),
% 1.40/1.58      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.40/1.58  thf('30', plain,
% 1.40/1.58      (![X0 : $i, X1 : $i]:
% 1.40/1.58         (~ (l1_pre_topc @ X0)
% 1.40/1.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.40/1.58          | ((k1_xboole_0) = (X1))
% 1.40/1.58          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 1.40/1.58          | ~ (v2_tex_2 @ X1 @ X0)
% 1.40/1.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['28', '29'])).
% 1.40/1.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.40/1.58  thf('31', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.40/1.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.40/1.58  thf('32', plain,
% 1.40/1.58      (![X0 : $i, X1 : $i]:
% 1.40/1.58         (~ (l1_pre_topc @ X0)
% 1.40/1.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.40/1.58          | ((k1_xboole_0) = (X1))
% 1.40/1.58          | ~ (v2_tex_2 @ X1 @ X0)
% 1.40/1.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.40/1.58      inference('demod', [status(thm)], ['30', '31'])).
% 1.40/1.58  thf('33', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.40/1.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.40/1.58          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.40/1.58          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 1.40/1.58          | ~ (l1_pre_topc @ X0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['27', '32'])).
% 1.40/1.58  thf(t1_boole, axiom,
% 1.40/1.58    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.40/1.58  thf('34', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 1.40/1.58      inference('cnf', [status(esa)], [t1_boole])).
% 1.40/1.58  thf(t49_zfmisc_1, axiom,
% 1.40/1.58    (![A:$i,B:$i]:
% 1.40/1.58     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.40/1.58  thf('35', plain,
% 1.40/1.58      (![X5 : $i, X6 : $i]:
% 1.40/1.58         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 1.40/1.58      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.40/1.58  thf('36', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['34', '35'])).
% 1.40/1.58  thf('37', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.40/1.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.40/1.58          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.40/1.58          | ~ (l1_pre_topc @ X0))),
% 1.40/1.58      inference('simplify_reflect-', [status(thm)], ['33', '36'])).
% 1.40/1.58  thf('38', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.40/1.58          | ~ (l1_pre_topc @ X0)
% 1.40/1.58          | ~ (v2_pre_topc @ X0)
% 1.40/1.58          | (v2_struct_0 @ X0)
% 1.40/1.58          | ~ (l1_pre_topc @ X0)
% 1.40/1.58          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.40/1.58          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.40/1.58      inference('sup-', [status(thm)], ['20', '37'])).
% 1.40/1.58  thf('39', plain,
% 1.40/1.58      (![X0 : $i]:
% 1.40/1.58         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.40/1.58          | (v2_struct_0 @ X0)
% 1.40/1.58          | ~ (v2_pre_topc @ X0)
% 1.40/1.58          | ~ (l1_pre_topc @ X0)
% 1.40/1.58          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.40/1.58      inference('simplify', [status(thm)], ['38'])).
% 1.40/1.58  thf('40', plain,
% 1.40/1.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.40/1.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.40/1.58        | ~ (l1_pre_topc @ sk_A)
% 1.40/1.58        | ~ (v2_pre_topc @ sk_A)
% 1.40/1.58        | (v2_struct_0 @ sk_A))),
% 1.40/1.58      inference('sup-', [status(thm)], ['9', '39'])).
% 1.40/1.58  thf('41', plain, ((v1_xboole_0 @ sk_B_2)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf('42', plain, (((sk_B_2) = (k1_xboole_0))),
% 1.40/1.58      inference('sup-', [status(thm)], ['5', '6'])).
% 1.40/1.58  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.40/1.58      inference('demod', [status(thm)], ['41', '42'])).
% 1.40/1.58  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf('46', plain,
% 1.40/1.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 1.40/1.58      inference('demod', [status(thm)], ['40', '43', '44', '45'])).
% 1.40/1.58  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf('48', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.40/1.58      inference('clc', [status(thm)], ['46', '47'])).
% 1.40/1.58  thf(fc2_struct_0, axiom,
% 1.40/1.58    (![A:$i]:
% 1.40/1.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.40/1.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.40/1.58  thf('49', plain,
% 1.40/1.58      (![X18 : $i]:
% 1.40/1.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 1.40/1.58          | ~ (l1_struct_0 @ X18)
% 1.40/1.58          | (v2_struct_0 @ X18))),
% 1.40/1.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.40/1.58  thf('50', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 1.40/1.58      inference('sup-', [status(thm)], ['48', '49'])).
% 1.40/1.58  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.40/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.40/1.58  thf(dt_l1_pre_topc, axiom,
% 1.40/1.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.40/1.58  thf('52', plain,
% 1.40/1.58      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 1.40/1.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.40/1.58  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 1.40/1.58      inference('sup-', [status(thm)], ['51', '52'])).
% 1.40/1.58  thf('54', plain, ((v2_struct_0 @ sk_A)),
% 1.40/1.58      inference('demod', [status(thm)], ['50', '53'])).
% 1.40/1.58  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 1.40/1.58  
% 1.40/1.58  % SZS output end Refutation
% 1.40/1.58  
% 1.40/1.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
