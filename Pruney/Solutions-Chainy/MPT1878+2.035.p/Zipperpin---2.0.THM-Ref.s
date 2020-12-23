%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x1jWpkj2He

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:08 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 117 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  574 ( 943 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
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

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_tex_2 @ X22 @ X23 )
      | ~ ( v2_tex_2 @ X24 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( X22 = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','47'])).

thf('49',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x1jWpkj2He
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.62  % Solved by: fo/fo7.sh
% 0.45/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.62  % done 252 iterations in 0.168s
% 0.45/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.62  % SZS output start Refutation
% 0.45/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.45/0.62  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.45/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.62  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.45/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.62  thf(t46_tex_2, conjecture,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( ( v1_xboole_0 @ B ) & 
% 0.45/0.62             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.62           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.45/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.62    (~( ![A:$i]:
% 0.45/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.62            ( l1_pre_topc @ A ) ) =>
% 0.45/0.62          ( ![B:$i]:
% 0.45/0.62            ( ( ( v1_xboole_0 @ B ) & 
% 0.45/0.62                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.62              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.45/0.62    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.45/0.62  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(d1_xboole_0, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.62  thf('1', plain,
% 0.45/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.62  thf('2', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('3', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(l13_xboole_0, axiom,
% 0.45/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.62  thf('4', plain,
% 0.45/0.62      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.45/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.62  thf('5', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.62  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.45/0.62      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.62  thf('7', plain,
% 0.45/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.62  thf(t1_subset, axiom,
% 0.45/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.62  thf('8', plain,
% 0.45/0.62      (![X11 : $i, X12 : $i]:
% 0.45/0.62         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.45/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.62  thf('9', plain,
% 0.45/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.45/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.45/0.62  thf('10', plain,
% 0.45/0.62      (![X20 : $i, X21 : $i]:
% 0.45/0.62         ((v1_xboole_0 @ X20)
% 0.45/0.62          | ~ (m1_subset_1 @ X21 @ X20)
% 0.45/0.62          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.45/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.45/0.62  thf('11', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v1_xboole_0 @ X0)
% 0.45/0.62          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.45/0.62          | (v1_xboole_0 @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.62  thf('12', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.45/0.62          | (v1_xboole_0 @ X0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.62  thf('13', plain,
% 0.45/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.62  thf(t36_tex_2, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.62           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.45/0.62  thf('14', plain,
% 0.45/0.62      (![X25 : $i, X26 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.45/0.62          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 0.45/0.62          | ~ (l1_pre_topc @ X26)
% 0.45/0.62          | ~ (v2_pre_topc @ X26)
% 0.45/0.62          | (v2_struct_0 @ X26))),
% 0.45/0.62      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.45/0.62  thf('15', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.62          | (v2_struct_0 @ X0)
% 0.45/0.62          | ~ (v2_pre_topc @ X0)
% 0.45/0.62          | ~ (l1_pre_topc @ X0)
% 0.45/0.62          | (v2_tex_2 @ 
% 0.45/0.62             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.45/0.62             X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.62  thf('16', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.45/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.62          | ~ (l1_pre_topc @ X0)
% 0.45/0.62          | ~ (v2_pre_topc @ X0)
% 0.45/0.62          | (v2_struct_0 @ X0)
% 0.45/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.45/0.62      inference('sup+', [status(thm)], ['12', '15'])).
% 0.45/0.62  thf('17', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v2_struct_0 @ X0)
% 0.45/0.62          | ~ (v2_pre_topc @ X0)
% 0.45/0.62          | ~ (l1_pre_topc @ X0)
% 0.45/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.62          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.62  thf('18', plain,
% 0.45/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.62  thf(t63_subset_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.45/0.62       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.62  thf('19', plain,
% 0.45/0.62      (![X9 : $i, X10 : $i]:
% 0.45/0.62         ((m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X10))
% 0.45/0.62          | ~ (r2_hidden @ X9 @ X10))),
% 0.45/0.62      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.45/0.62  thf('20', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v1_xboole_0 @ X0)
% 0.45/0.62          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.62  thf(t4_subset_1, axiom,
% 0.45/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.62  thf('21', plain,
% 0.45/0.62      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.45/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.62  thf(d7_tex_2, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( l1_pre_topc @ A ) =>
% 0.45/0.62       ( ![B:$i]:
% 0.45/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.62           ( ( v3_tex_2 @ B @ A ) <=>
% 0.45/0.62             ( ( v2_tex_2 @ B @ A ) & 
% 0.45/0.62               ( ![C:$i]:
% 0.45/0.62                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.62                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.62                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.62  thf('22', plain,
% 0.45/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.45/0.62          | ~ (v3_tex_2 @ X22 @ X23)
% 0.45/0.62          | ~ (v2_tex_2 @ X24 @ X23)
% 0.45/0.62          | ~ (r1_tarski @ X22 @ X24)
% 0.45/0.62          | ((X22) = (X24))
% 0.45/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.45/0.62          | ~ (l1_pre_topc @ X23))),
% 0.45/0.62      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.45/0.62  thf('23', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (~ (l1_pre_topc @ X0)
% 0.45/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | ((k1_xboole_0) = (X1))
% 0.45/0.62          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.45/0.62          | ~ (v2_tex_2 @ X1 @ X0)
% 0.45/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.62  thf('24', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.45/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.62  thf('25', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (~ (l1_pre_topc @ X0)
% 0.45/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.62          | ((k1_xboole_0) = (X1))
% 0.45/0.62          | ~ (v2_tex_2 @ X1 @ X0)
% 0.45/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.62  thf('26', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.62          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.45/0.62          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.45/0.62          | ~ (l1_pre_topc @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['20', '25'])).
% 0.45/0.62  thf(t1_boole, axiom,
% 0.45/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.62  thf('27', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.45/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.62  thf(t49_zfmisc_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.45/0.62  thf('28', plain,
% 0.45/0.62      (![X6 : $i, X7 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.45/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.45/0.62  thf('29', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.62  thf('30', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.62          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.45/0.62          | ~ (l1_pre_topc @ X0))),
% 0.45/0.62      inference('simplify_reflect-', [status(thm)], ['26', '29'])).
% 0.45/0.62  thf('31', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.62          | ~ (l1_pre_topc @ X0)
% 0.45/0.62          | ~ (v2_pre_topc @ X0)
% 0.45/0.62          | (v2_struct_0 @ X0)
% 0.45/0.62          | ~ (l1_pre_topc @ X0)
% 0.45/0.62          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['17', '30'])).
% 0.45/0.62  thf('32', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.62          | (v2_struct_0 @ X0)
% 0.45/0.62          | ~ (v2_pre_topc @ X0)
% 0.45/0.62          | ~ (l1_pre_topc @ X0)
% 0.45/0.62          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.45/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.62  thf('33', plain,
% 0.45/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.62        | (v2_struct_0 @ sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['6', '32'])).
% 0.45/0.62  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('36', plain,
% 0.45/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.45/0.62      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.45/0.62  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('38', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.45/0.62  thf(rc7_pre_topc, axiom,
% 0.45/0.62    (![A:$i]:
% 0.45/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.62       ( ?[B:$i]:
% 0.45/0.62         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.45/0.62           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.62  thf('39', plain,
% 0.45/0.62      (![X19 : $i]:
% 0.45/0.62         ((m1_subset_1 @ (sk_B_1 @ X19) @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.62          | ~ (l1_pre_topc @ X19)
% 0.45/0.62          | ~ (v2_pre_topc @ X19)
% 0.45/0.62          | (v2_struct_0 @ X19))),
% 0.45/0.62      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.45/0.62  thf(t5_subset, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.62  thf('40', plain,
% 0.45/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X16 @ X17)
% 0.45/0.62          | ~ (v1_xboole_0 @ X18)
% 0.45/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.62  thf('41', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((v2_struct_0 @ X0)
% 0.45/0.62          | ~ (v2_pre_topc @ X0)
% 0.45/0.62          | ~ (l1_pre_topc @ X0)
% 0.45/0.62          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.62          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.62  thf('42', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.45/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.62          | (v2_struct_0 @ sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['38', '41'])).
% 0.45/0.62  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('45', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.45/0.62      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.45/0.62  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 0.45/0.62      inference('clc', [status(thm)], ['45', '46'])).
% 0.45/0.62  thf('48', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.45/0.62      inference('sup-', [status(thm)], ['1', '47'])).
% 0.45/0.62  thf('49', plain,
% 0.45/0.62      (![X19 : $i]:
% 0.45/0.62         (~ (v1_xboole_0 @ (sk_B_1 @ X19))
% 0.45/0.63          | ~ (l1_pre_topc @ X19)
% 0.45/0.63          | ~ (v2_pre_topc @ X19)
% 0.45/0.63          | (v2_struct_0 @ X19))),
% 0.45/0.63      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.63  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('53', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.45/0.63  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
