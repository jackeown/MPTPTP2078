%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MDcj0Z6TiF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 264 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :  780 (5180 expanded)
%              Number of equality atoms :   13 ( 115 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_tex_2 @ X19 @ X20 )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
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
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X22 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('23',plain,(
    ! [X22: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X22 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X22 ) )
      | ~ ( r2_hidden @ X22 @ sk_B_1 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ X21 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ ( sk_C @ X19 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X3 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v4_pre_topc @ X18 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('42',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('47',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['42','43','44','50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','52','53','54'])).

thf('56',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['9','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MDcj0Z6TiF
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:20:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 171 iterations in 0.084s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(t58_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.54         ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                 ( ( r2_hidden @ C @ B ) =>
% 0.21/0.54                   ( ( k9_subset_1 @
% 0.21/0.54                       ( u1_struct_0 @ A ) @ B @ 
% 0.21/0.54                       ( k2_pre_topc @
% 0.21/0.54                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.21/0.54                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.21/0.54             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( ( ![C:$i]:
% 0.21/0.54                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                    ( ( r2_hidden @ C @ B ) =>
% 0.21/0.54                      ( ( k9_subset_1 @
% 0.21/0.54                          ( u1_struct_0 @ A ) @ B @ 
% 0.21/0.54                          ( k2_pre_topc @
% 0.21/0.54                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.21/0.54                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.21/0.54                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t37_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.54                      ( ![D:$i]:
% 0.21/0.54                        ( ( m1_subset_1 @
% 0.21/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.54                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.54             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.54          | (v2_tex_2 @ X19 @ X20)
% 0.21/0.54          | (r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 0.21/0.54          | ~ (l1_pre_topc @ X20)
% 0.21/0.54          | ~ (v2_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.21/0.54        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.21/0.54        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.54  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.54        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf('8', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.21/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t5_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.54          | ~ (v1_xboole_0 @ X10)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.21/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t4_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.54          | (m1_subset_1 @ X5 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X13)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ X13)
% 0.21/0.54          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.54          = (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.21/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X22 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X22 @ sk_B_1)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.21/0.54              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X22)))
% 0.21/0.54              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X22))
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X22 : $i]:
% 0.21/0.54         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.21/0.54            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X22)))
% 0.21/0.54            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X22))
% 0.21/0.54          | ~ (r2_hidden @ X22 @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.21/0.54         (k2_pre_topc @ sk_A @ 
% 0.21/0.54          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.54         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.21/0.54          (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))))
% 0.21/0.54          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['19', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.54          | (v2_tex_2 @ X19 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.54          | ~ (v3_pre_topc @ X21 @ X20)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ X21)
% 0.21/0.54              != (k6_domain_1 @ (u1_struct_0 @ X20) @ (sk_C @ X19 @ X20)))
% 0.21/0.54          | ~ (l1_pre_topc @ X20)
% 0.21/0.54          | ~ (v2_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.54          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ~ (v3_pre_topc @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.21/0.54        | ~ (m1_subset_1 @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.54        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('30', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.21/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l3_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.54          | (r2_hidden @ X0 @ X2)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.54  thf(t63_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_tarski @ X3) @ (k1_zfmisc_1 @ X4))
% 0.21/0.54          | ~ (r2_hidden @ X3 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf(dt_k2_pre_topc, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.54          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (((m1_subset_1 @ 
% 0.21/0.54         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((m1_subset_1 @ 
% 0.21/0.54        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf(t24_tdlat_3, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.54         ( ![B:$i]:
% 0.21/0.54           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (v3_tdlat_3 @ X17)
% 0.21/0.54          | ~ (v4_pre_topc @ X18 @ X17)
% 0.21/0.54          | (v3_pre_topc @ X18 @ X17)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.54          | ~ (l1_pre_topc @ X17)
% 0.21/0.54          | ~ (v2_pre_topc @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v3_pre_topc @ 
% 0.21/0.54           (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.21/0.54        | ~ (v4_pre_topc @ 
% 0.21/0.54             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.21/0.54        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf(fc1_tops_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X15)
% 0.21/0.54          | ~ (v2_pre_topc @ X15)
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.54          | (v4_pre_topc @ (k2_pre_topc @ X15 @ X16) @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((v4_pre_topc @ 
% 0.21/0.54         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((v4_pre_topc @ 
% 0.21/0.54        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.54  thf('51', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((v3_pre_topc @ 
% 0.21/0.54        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43', '44', '50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((m1_subset_1 @ 
% 0.21/0.54        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.54          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['27', '28', '29', '52', '53', '54'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.54  thf('57', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['12', '60'])).
% 0.21/0.54  thf('62', plain, ($false), inference('sup-', [status(thm)], ['9', '61'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
