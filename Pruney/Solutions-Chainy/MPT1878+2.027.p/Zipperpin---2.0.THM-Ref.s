%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JuEM937SIA

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:06 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 116 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  563 ( 934 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
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
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X6 ) @ X6 ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_2 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ ( sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_2 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JuEM937SIA
% 0.16/0.36  % Computer   : n022.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 09:22:56 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 557 iterations in 0.354s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.83  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.60/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.83  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.60/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.83  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.60/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.83  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.60/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.83  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.60/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.83  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.60/0.83  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.60/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.60/0.83  thf(t46_tex_2, conjecture,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( ( v1_xboole_0 @ B ) & 
% 0.60/0.83             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.83           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i]:
% 0.60/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.83            ( l1_pre_topc @ A ) ) =>
% 0.60/0.83          ( ![B:$i]:
% 0.60/0.83            ( ( ( v1_xboole_0 @ B ) & 
% 0.60/0.83                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.83              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.60/0.83  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(d1_xboole_0, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.60/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.83  thf('2', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('3', plain, ((v1_xboole_0 @ sk_B_3)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(l13_xboole_0, axiom,
% 0.60/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.83  thf('4', plain,
% 0.60/0.83      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.60/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.83  thf('5', plain, (((sk_B_3) = (k1_xboole_0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.60/0.83      inference('demod', [status(thm)], ['2', '5'])).
% 0.60/0.83  thf(existence_m1_subset_1, axiom,
% 0.60/0.83    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.60/0.83  thf('7', plain, (![X6 : $i]: (m1_subset_1 @ (sk_B_1 @ X6) @ X6)),
% 0.60/0.83      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.60/0.83  thf(redefinition_k6_domain_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.60/0.83       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.60/0.83  thf('8', plain,
% 0.60/0.83      (![X17 : $i, X18 : $i]:
% 0.60/0.83         ((v1_xboole_0 @ X17)
% 0.60/0.83          | ~ (m1_subset_1 @ X18 @ X17)
% 0.60/0.83          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.60/0.83      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.60/0.83  thf('9', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.60/0.83          | (v1_xboole_0 @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('10', plain, (![X6 : $i]: (m1_subset_1 @ (sk_B_1 @ X6) @ X6)),
% 0.60/0.83      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.60/0.83  thf(t36_tex_2, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.83           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.60/0.83  thf('11', plain,
% 0.60/0.83      (![X22 : $i, X23 : $i]:
% 0.60/0.83         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.60/0.83          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.60/0.83          | ~ (l1_pre_topc @ X23)
% 0.60/0.83          | ~ (v2_pre_topc @ X23)
% 0.60/0.83          | (v2_struct_0 @ X23))),
% 0.60/0.83      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.60/0.83  thf('12', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((v2_struct_0 @ X0)
% 0.60/0.83          | ~ (v2_pre_topc @ X0)
% 0.60/0.83          | ~ (l1_pre_topc @ X0)
% 0.60/0.83          | (v2_tex_2 @ 
% 0.60/0.83             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B_1 @ (u1_struct_0 @ X0))) @ 
% 0.60/0.83             X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.83  thf('13', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.60/0.83          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.60/0.83          | ~ (l1_pre_topc @ X0)
% 0.60/0.83          | ~ (v2_pre_topc @ X0)
% 0.60/0.83          | (v2_struct_0 @ X0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['9', '12'])).
% 0.60/0.83  thf('14', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.60/0.83          | (v1_xboole_0 @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('15', plain, (![X6 : $i]: (m1_subset_1 @ (sk_B_1 @ X6) @ X6)),
% 0.60/0.83      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.60/0.83  thf(dt_k6_domain_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.60/0.83       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.83  thf('16', plain,
% 0.60/0.83      (![X15 : $i, X16 : $i]:
% 0.60/0.83         ((v1_xboole_0 @ X15)
% 0.60/0.83          | ~ (m1_subset_1 @ X16 @ X15)
% 0.60/0.83          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.60/0.83  thf('17', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B_1 @ X0)) @ 
% 0.60/0.83           (k1_zfmisc_1 @ X0))
% 0.60/0.83          | (v1_xboole_0 @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.83  thf('18', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((m1_subset_1 @ (k1_tarski @ (sk_B_1 @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.60/0.83          | (v1_xboole_0 @ X0)
% 0.60/0.83          | (v1_xboole_0 @ X0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['14', '17'])).
% 0.60/0.83  thf('19', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((v1_xboole_0 @ X0)
% 0.60/0.83          | (m1_subset_1 @ (k1_tarski @ (sk_B_1 @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.60/0.83      inference('simplify', [status(thm)], ['18'])).
% 0.60/0.83  thf(t4_subset_1, axiom,
% 0.60/0.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.83  thf('20', plain,
% 0.60/0.83      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.60/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.83  thf(d7_tex_2, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( l1_pre_topc @ A ) =>
% 0.60/0.83       ( ![B:$i]:
% 0.60/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.83           ( ( v3_tex_2 @ B @ A ) <=>
% 0.60/0.83             ( ( v2_tex_2 @ B @ A ) & 
% 0.60/0.83               ( ![C:$i]:
% 0.60/0.83                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.83                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.60/0.83                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf('21', plain,
% 0.60/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.83         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.83          | ~ (v3_tex_2 @ X19 @ X20)
% 0.60/0.83          | ~ (v2_tex_2 @ X21 @ X20)
% 0.60/0.83          | ~ (r1_tarski @ X19 @ X21)
% 0.60/0.83          | ((X19) = (X21))
% 0.60/0.83          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.60/0.83          | ~ (l1_pre_topc @ X20))),
% 0.60/0.83      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.60/0.83  thf('22', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (l1_pre_topc @ X0)
% 0.60/0.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.60/0.83          | ((k1_xboole_0) = (X1))
% 0.60/0.83          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.60/0.83          | ~ (v2_tex_2 @ X1 @ X0)
% 0.60/0.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.83  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.83  thf('23', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.60/0.83      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.83  thf('24', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (l1_pre_topc @ X0)
% 0.60/0.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.60/0.83          | ((k1_xboole_0) = (X1))
% 0.60/0.83          | ~ (v2_tex_2 @ X1 @ X0)
% 0.60/0.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.60/0.83      inference('demod', [status(thm)], ['22', '23'])).
% 0.60/0.83  thf('25', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.60/0.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.83          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.60/0.83          | ((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))))
% 0.60/0.83          | ~ (l1_pre_topc @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['19', '24'])).
% 0.60/0.83  thf('26', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((v2_struct_0 @ X0)
% 0.60/0.83          | ~ (v2_pre_topc @ X0)
% 0.60/0.83          | ~ (l1_pre_topc @ X0)
% 0.60/0.83          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.60/0.83          | ~ (l1_pre_topc @ X0)
% 0.60/0.83          | ((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))))
% 0.60/0.83          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.83          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['13', '25'])).
% 0.60/0.83  thf('27', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.83          | ((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))))
% 0.60/0.83          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.60/0.83          | ~ (l1_pre_topc @ X0)
% 0.60/0.83          | ~ (v2_pre_topc @ X0)
% 0.60/0.83          | (v2_struct_0 @ X0))),
% 0.60/0.83      inference('simplify', [status(thm)], ['26'])).
% 0.60/0.83  thf('28', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_A)
% 0.60/0.83        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.83        | ((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ sk_A)))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['6', '27'])).
% 0.60/0.83  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('31', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_A)
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.60/0.83        | ((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ sk_A)))))),
% 0.60/0.83      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.60/0.83  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('33', plain,
% 0.60/0.83      ((((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.60/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.83      inference('clc', [status(thm)], ['31', '32'])).
% 0.60/0.83  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.60/0.83  thf('34', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 0.60/0.83      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.60/0.83  thf('35', plain,
% 0.60/0.83      ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.83  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.83  thf('37', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.60/0.83      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.83  thf(rc7_pre_topc, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.83       ( ?[B:$i]:
% 0.60/0.83         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.60/0.83           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.60/0.83  thf('38', plain,
% 0.60/0.83      (![X14 : $i]:
% 0.60/0.83         ((m1_subset_1 @ (sk_B_2 @ X14) @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.60/0.83          | ~ (l1_pre_topc @ X14)
% 0.60/0.83          | ~ (v2_pre_topc @ X14)
% 0.60/0.83          | (v2_struct_0 @ X14))),
% 0.60/0.83      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.60/0.83  thf(t5_subset, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.60/0.83          ( v1_xboole_0 @ C ) ) ))).
% 0.60/0.83  thf('39', plain,
% 0.60/0.83      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X11 @ X12)
% 0.60/0.83          | ~ (v1_xboole_0 @ X13)
% 0.60/0.83          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.60/0.83      inference('cnf', [status(esa)], [t5_subset])).
% 0.60/0.83  thf('40', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         ((v2_struct_0 @ X0)
% 0.60/0.83          | ~ (v2_pre_topc @ X0)
% 0.60/0.83          | ~ (l1_pre_topc @ X0)
% 0.60/0.83          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.60/0.83          | ~ (r2_hidden @ X1 @ (sk_B_2 @ X0)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.60/0.83  thf('41', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X0 @ (sk_B_2 @ sk_A))
% 0.60/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.60/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.60/0.83          | (v2_struct_0 @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['37', '40'])).
% 0.60/0.83  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('44', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X0 @ (sk_B_2 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.60/0.83      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.60/0.83  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_2 @ sk_A))),
% 0.60/0.83      inference('clc', [status(thm)], ['44', '45'])).
% 0.60/0.83  thf('47', plain, ((v1_xboole_0 @ (sk_B_2 @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['1', '46'])).
% 0.60/0.83  thf('48', plain,
% 0.60/0.83      (![X14 : $i]:
% 0.60/0.83         (~ (v1_xboole_0 @ (sk_B_2 @ X14))
% 0.60/0.83          | ~ (l1_pre_topc @ X14)
% 0.60/0.83          | ~ (v2_pre_topc @ X14)
% 0.60/0.83          | (v2_struct_0 @ X14))),
% 0.60/0.83      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.60/0.83  thf('49', plain,
% 0.60/0.83      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.83  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('52', plain, ((v2_struct_0 @ sk_A)),
% 0.60/0.83      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.60/0.83  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.60/0.83  
% 0.60/0.83  % SZS output end Refutation
% 0.60/0.83  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
