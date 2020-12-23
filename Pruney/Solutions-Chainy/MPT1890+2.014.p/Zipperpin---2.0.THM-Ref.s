%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nv3NsjmV6F

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:33 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 274 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          :  799 (5237 expanded)
%              Number of equality atoms :   13 ( 115 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t58_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
             => ( v2_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v2_tex_2 @ X24 @ X25 )
      | ( r2_hidden @ ( sk_C @ X24 @ X25 ) @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('19',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
      = ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('21',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X27 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('23',plain,(
    ! [X27: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X27 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ X26 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ ( sk_C @ X24 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_tdlat_3 @ X22 )
      | ~ ( v4_pre_topc @ X23 @ X22 )
      | ( v3_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('49',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
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
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','46','52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','54','55','56'])).

thf('58',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','62'])).

thf('64',plain,(
    $false ),
    inference('sup-',[status(thm)],['9','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nv3NsjmV6F
% 0.14/0.37  % Computer   : n018.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:13:42 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 202 iterations in 0.134s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.44/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.44/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.62  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(t58_tex_2, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.44/0.62         ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( ![C:$i]:
% 0.44/0.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                 ( ( r2_hidden @ C @ B ) =>
% 0.44/0.62                   ( ( k9_subset_1 @
% 0.44/0.62                       ( u1_struct_0 @ A ) @ B @ 
% 0.44/0.62                       ( k2_pre_topc @
% 0.44/0.62                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.44/0.62                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.44/0.62             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.62            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62              ( ( ![C:$i]:
% 0.44/0.62                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                    ( ( r2_hidden @ C @ B ) =>
% 0.44/0.62                      ( ( k9_subset_1 @
% 0.44/0.62                          ( u1_struct_0 @ A ) @ B @ 
% 0.44/0.62                          ( k2_pre_topc @
% 0.44/0.62                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.44/0.62                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.44/0.62                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t37_tex_2, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( ![C:$i]:
% 0.44/0.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.44/0.62                      ( ![D:$i]:
% 0.44/0.62                        ( ( m1_subset_1 @
% 0.44/0.62                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.44/0.62                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.44/0.62                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.44/0.62             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X24 : $i, X25 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.62          | (v2_tex_2 @ X24 @ X25)
% 0.44/0.62          | (r2_hidden @ (sk_C @ X24 @ X25) @ X24)
% 0.44/0.62          | ~ (l1_pre_topc @ X25)
% 0.44/0.62          | ~ (v2_pre_topc @ X25)
% 0.44/0.62          | (v2_struct_0 @ X25))),
% 0.44/0.62      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.44/0.62        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.62  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.44/0.62        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.44/0.62  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.62        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.44/0.62      inference('clc', [status(thm)], ['5', '6'])).
% 0.44/0.62  thf('8', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('9', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.44/0.62      inference('clc', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t5_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.44/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X13 @ X14)
% 0.44/0.62          | ~ (v1_xboole_0 @ X15)
% 0.44/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.62  thf('13', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.44/0.62      inference('clc', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t4_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.44/0.62       ( m1_subset_1 @ A @ C ) ))).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X10 @ X11)
% 0.44/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.44/0.62          | (m1_subset_1 @ X10 @ X12))),
% 0.44/0.62      inference('cnf', [status(esa)], [t4_subset])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '16'])).
% 0.44/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.44/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X18 : $i, X19 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X18)
% 0.44/0.62          | ~ (m1_subset_1 @ X19 @ X18)
% 0.44/0.62          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.44/0.62          = (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)))
% 0.44/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('20', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.44/0.62      inference('clc', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X27 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X27 @ sk_B_1)
% 0.44/0.62          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.44/0.62              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X27)))
% 0.44/0.62              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X27))
% 0.44/0.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X27 : $i]:
% 0.44/0.62         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.44/0.62            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X27)))
% 0.44/0.62            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X27))
% 0.44/0.62          | ~ (r2_hidden @ X27 @ sk_B_1))),
% 0.44/0.62      inference('clc', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.44/0.62         (k2_pre_topc @ sk_A @ 
% 0.44/0.62          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.44/0.62         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['20', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.44/0.62          (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))))
% 0.44/0.62          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.44/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['19', '24'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.62          | (v2_tex_2 @ X24 @ X25)
% 0.44/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.62          | ~ (v3_pre_topc @ X26 @ X25)
% 0.44/0.62          | ((k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ X26)
% 0.44/0.62              != (k6_domain_1 @ (u1_struct_0 @ X25) @ (sk_C @ X24 @ X25)))
% 0.44/0.62          | ~ (l1_pre_topc @ X25)
% 0.44/0.62          | ~ (v2_pre_topc @ X25)
% 0.44/0.62          | (v2_struct_0 @ X25))),
% 0.44/0.62      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.44/0.62          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.44/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ~ (v3_pre_topc @ 
% 0.44/0.62             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.44/0.62        | ~ (m1_subset_1 @ 
% 0.44/0.62             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.62  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('30', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.44/0.62      inference('clc', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(l3_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X4 @ X5)
% 0.44/0.62          | (r2_hidden @ X4 @ X6)
% 0.44/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.44/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['30', '33'])).
% 0.44/0.62  thf(l1_zfmisc_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X1 : $i, X3 : $i]:
% 0.44/0.62         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      ((r1_tarski @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)) @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.62  thf(t3_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      (![X7 : $i, X9 : $i]:
% 0.44/0.62         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      ((m1_subset_1 @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf(dt_k2_pre_topc, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.44/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62       ( m1_subset_1 @
% 0.44/0.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X16)
% 0.44/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.44/0.62          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 0.44/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (((m1_subset_1 @ 
% 0.44/0.62         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.44/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.62  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      ((m1_subset_1 @ 
% 0.44/0.62        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.44/0.62  thf(t24_tdlat_3, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ( v3_tdlat_3 @ A ) <=>
% 0.44/0.62         ( ![B:$i]:
% 0.44/0.62           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X22 : $i, X23 : $i]:
% 0.44/0.62         (~ (v3_tdlat_3 @ X22)
% 0.44/0.62          | ~ (v4_pre_topc @ X23 @ X22)
% 0.44/0.62          | (v3_pre_topc @ X23 @ X22)
% 0.44/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.44/0.62          | ~ (l1_pre_topc @ X22)
% 0.44/0.62          | ~ (v2_pre_topc @ X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      ((~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | (v3_pre_topc @ 
% 0.44/0.62           (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.44/0.62        | ~ (v4_pre_topc @ 
% 0.44/0.62             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.44/0.62        | ~ (v3_tdlat_3 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.62  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      ((m1_subset_1 @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf(fc1_tops_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.44/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (![X20 : $i, X21 : $i]:
% 0.44/0.62         (~ (l1_pre_topc @ X20)
% 0.44/0.62          | ~ (v2_pre_topc @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.62          | (v4_pre_topc @ (k2_pre_topc @ X20 @ X21) @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (((v4_pre_topc @ 
% 0.44/0.62         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.44/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.62  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('52', plain,
% 0.44/0.62      ((v4_pre_topc @ 
% 0.44/0.62        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.44/0.62  thf('53', plain, ((v3_tdlat_3 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('54', plain,
% 0.44/0.62      ((v3_pre_topc @ 
% 0.44/0.62        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.44/0.62      inference('demod', [status(thm)], ['44', '45', '46', '52', '53'])).
% 0.44/0.62  thf('55', plain,
% 0.44/0.62      ((m1_subset_1 @ 
% 0.44/0.62        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('57', plain,
% 0.44/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.44/0.62          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.44/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['27', '28', '29', '54', '55', '56'])).
% 0.44/0.62  thf('58', plain,
% 0.44/0.62      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['57'])).
% 0.44/0.62  thf('59', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('60', plain,
% 0.44/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.44/0.62      inference('clc', [status(thm)], ['58', '59'])).
% 0.44/0.62  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('62', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('63', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.44/0.62      inference('demod', [status(thm)], ['12', '62'])).
% 0.44/0.62  thf('64', plain, ($false), inference('sup-', [status(thm)], ['9', '63'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
