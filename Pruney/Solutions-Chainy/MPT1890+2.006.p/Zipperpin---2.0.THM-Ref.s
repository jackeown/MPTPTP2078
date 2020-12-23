%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9czyddDz0h

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:31 EST 2020

% Result     : Theorem 6.92s
% Output     : Refutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 658 expanded)
%              Number of leaves         :   32 ( 204 expanded)
%              Depth                    :   18
%              Number of atoms          :  919 (11528 expanded)
%              Number of equality atoms :   22 ( 257 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tex_2 @ X27 @ X28 )
      | ( r2_hidden @ ( sk_C_1 @ X27 @ X28 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
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
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X30 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('30',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','25'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('33',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('35',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('37',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('40',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v2_tex_2 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X28 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ X29 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ ( sk_C_1 @ X27 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
       != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
       != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
     != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_tdlat_3 @ X25 )
      | ~ ( v4_pre_topc @ X26 @ X25 )
      | ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('57',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('61',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('62',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['57','58','59','65','66'])).

thf('68',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
     != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','67'])).

thf('69',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
     != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
 != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9czyddDz0h
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.92/7.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.92/7.13  % Solved by: fo/fo7.sh
% 6.92/7.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.92/7.13  % done 2287 iterations in 6.669s
% 6.92/7.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.92/7.13  % SZS output start Refutation
% 6.92/7.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.92/7.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.92/7.13  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 6.92/7.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.92/7.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.92/7.13  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.92/7.13  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 6.92/7.13  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 6.92/7.13  thf(sk_A_type, type, sk_A: $i).
% 6.92/7.13  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 6.92/7.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.92/7.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.92/7.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.92/7.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.92/7.13  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.92/7.13  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 6.92/7.13  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 6.92/7.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.92/7.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.92/7.13  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.92/7.13  thf(t58_tex_2, conjecture,
% 6.92/7.13    (![A:$i]:
% 6.92/7.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 6.92/7.13         ( l1_pre_topc @ A ) ) =>
% 6.92/7.13       ( ![B:$i]:
% 6.92/7.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.92/7.13           ( ( ![C:$i]:
% 6.92/7.13               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.92/7.13                 ( ( r2_hidden @ C @ B ) =>
% 6.92/7.13                   ( ( k9_subset_1 @
% 6.92/7.13                       ( u1_struct_0 @ A ) @ B @ 
% 6.92/7.13                       ( k2_pre_topc @
% 6.92/7.13                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 6.92/7.13                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 6.92/7.13             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 6.92/7.13  thf(zf_stmt_0, negated_conjecture,
% 6.92/7.13    (~( ![A:$i]:
% 6.92/7.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.92/7.13            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.92/7.13          ( ![B:$i]:
% 6.92/7.13            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.92/7.13              ( ( ![C:$i]:
% 6.92/7.13                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.92/7.13                    ( ( r2_hidden @ C @ B ) =>
% 6.92/7.13                      ( ( k9_subset_1 @
% 6.92/7.13                          ( u1_struct_0 @ A ) @ B @ 
% 6.92/7.13                          ( k2_pre_topc @
% 6.92/7.13                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 6.92/7.13                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 6.92/7.13                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 6.92/7.13    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 6.92/7.13  thf('0', plain,
% 6.92/7.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf(t37_tex_2, axiom,
% 6.92/7.13    (![A:$i]:
% 6.92/7.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.92/7.13       ( ![B:$i]:
% 6.92/7.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.92/7.13           ( ( ![C:$i]:
% 6.92/7.13               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.92/7.13                 ( ~( ( r2_hidden @ C @ B ) & 
% 6.92/7.13                      ( ![D:$i]:
% 6.92/7.13                        ( ( m1_subset_1 @
% 6.92/7.13                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.92/7.13                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 6.92/7.13                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 6.92/7.13                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 6.92/7.13             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 6.92/7.13  thf('1', plain,
% 6.92/7.13      (![X27 : $i, X28 : $i]:
% 6.92/7.13         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 6.92/7.13          | (v2_tex_2 @ X27 @ X28)
% 6.92/7.13          | (r2_hidden @ (sk_C_1 @ X27 @ X28) @ X27)
% 6.92/7.13          | ~ (l1_pre_topc @ X28)
% 6.92/7.13          | ~ (v2_pre_topc @ X28)
% 6.92/7.13          | (v2_struct_0 @ X28))),
% 6.92/7.13      inference('cnf', [status(esa)], [t37_tex_2])).
% 6.92/7.13  thf('2', plain,
% 6.92/7.13      (((v2_struct_0 @ sk_A)
% 6.92/7.13        | ~ (v2_pre_topc @ sk_A)
% 6.92/7.13        | ~ (l1_pre_topc @ sk_A)
% 6.92/7.13        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 6.92/7.13        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['0', '1'])).
% 6.92/7.13  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('5', plain,
% 6.92/7.13      (((v2_struct_0 @ sk_A)
% 6.92/7.13        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 6.92/7.13        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 6.92/7.13      inference('demod', [status(thm)], ['2', '3', '4'])).
% 6.92/7.13  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('7', plain,
% 6.92/7.13      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 6.92/7.13        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 6.92/7.13      inference('clc', [status(thm)], ['5', '6'])).
% 6.92/7.13  thf('8', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('9', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 6.92/7.13      inference('clc', [status(thm)], ['7', '8'])).
% 6.92/7.13  thf('10', plain,
% 6.92/7.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf(t3_subset, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.92/7.13  thf('11', plain,
% 6.92/7.13      (![X13 : $i, X14 : $i]:
% 6.92/7.13         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 6.92/7.13      inference('cnf', [status(esa)], [t3_subset])).
% 6.92/7.13  thf('12', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['10', '11'])).
% 6.92/7.13  thf(d3_tarski, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( r1_tarski @ A @ B ) <=>
% 6.92/7.13       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.92/7.13  thf('13', plain,
% 6.92/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.92/7.13         (~ (r2_hidden @ X0 @ X1)
% 6.92/7.13          | (r2_hidden @ X0 @ X2)
% 6.92/7.13          | ~ (r1_tarski @ X1 @ X2))),
% 6.92/7.13      inference('cnf', [status(esa)], [d3_tarski])).
% 6.92/7.13  thf('14', plain,
% 6.92/7.13      (![X0 : $i]:
% 6.92/7.13         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 6.92/7.13      inference('sup-', [status(thm)], ['12', '13'])).
% 6.92/7.13  thf('15', plain,
% 6.92/7.13      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['9', '14'])).
% 6.92/7.13  thf(d2_subset_1, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( ( v1_xboole_0 @ A ) =>
% 6.92/7.13         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.92/7.13       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.92/7.13         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.92/7.13  thf('16', plain,
% 6.92/7.13      (![X10 : $i, X11 : $i]:
% 6.92/7.13         (~ (r2_hidden @ X10 @ X11)
% 6.92/7.13          | (m1_subset_1 @ X10 @ X11)
% 6.92/7.13          | (v1_xboole_0 @ X11))),
% 6.92/7.13      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.92/7.13  thf('17', plain,
% 6.92/7.13      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 6.92/7.13        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('sup-', [status(thm)], ['15', '16'])).
% 6.92/7.13  thf('18', plain,
% 6.92/7.13      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['9', '14'])).
% 6.92/7.13  thf(d10_xboole_0, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.92/7.13  thf('19', plain,
% 6.92/7.13      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 6.92/7.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.92/7.13  thf('20', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 6.92/7.13      inference('simplify', [status(thm)], ['19'])).
% 6.92/7.13  thf('21', plain,
% 6.92/7.13      (![X13 : $i, X15 : $i]:
% 6.92/7.13         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 6.92/7.13      inference('cnf', [status(esa)], [t3_subset])).
% 6.92/7.13  thf('22', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 6.92/7.13      inference('sup-', [status(thm)], ['20', '21'])).
% 6.92/7.13  thf(t5_subset, axiom,
% 6.92/7.13    (![A:$i,B:$i,C:$i]:
% 6.92/7.13     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 6.92/7.13          ( v1_xboole_0 @ C ) ) ))).
% 6.92/7.13  thf('23', plain,
% 6.92/7.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.92/7.13         (~ (r2_hidden @ X16 @ X17)
% 6.92/7.13          | ~ (v1_xboole_0 @ X18)
% 6.92/7.13          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 6.92/7.13      inference('cnf', [status(esa)], [t5_subset])).
% 6.92/7.13  thf('24', plain,
% 6.92/7.13      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 6.92/7.13      inference('sup-', [status(thm)], ['22', '23'])).
% 6.92/7.13  thf('25', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['18', '24'])).
% 6.92/7.13  thf('26', plain,
% 6.92/7.13      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('clc', [status(thm)], ['17', '25'])).
% 6.92/7.13  thf('27', plain,
% 6.92/7.13      (![X30 : $i]:
% 6.92/7.13         (~ (r2_hidden @ X30 @ sk_B_1)
% 6.92/7.13          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X30)))
% 6.92/7.13              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X30))
% 6.92/7.13          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('28', plain,
% 6.92/7.13      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13          (k2_pre_topc @ sk_A @ 
% 6.92/7.13           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 6.92/7.13          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 6.92/7.13        | ~ (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 6.92/7.13      inference('sup-', [status(thm)], ['26', '27'])).
% 6.92/7.13  thf('29', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 6.92/7.13      inference('clc', [status(thm)], ['7', '8'])).
% 6.92/7.13  thf('30', plain,
% 6.92/7.13      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13         (k2_pre_topc @ sk_A @ 
% 6.92/7.13          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 6.92/7.13         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 6.92/7.13      inference('demod', [status(thm)], ['28', '29'])).
% 6.92/7.13  thf('31', plain,
% 6.92/7.13      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('clc', [status(thm)], ['17', '25'])).
% 6.92/7.13  thf(redefinition_k6_domain_1, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 6.92/7.13       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 6.92/7.13  thf('32', plain,
% 6.92/7.13      (![X21 : $i, X22 : $i]:
% 6.92/7.13         ((v1_xboole_0 @ X21)
% 6.92/7.13          | ~ (m1_subset_1 @ X22 @ X21)
% 6.92/7.13          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 6.92/7.13      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 6.92/7.13  thf('33', plain,
% 6.92/7.13      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 6.92/7.13          = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 6.92/7.13        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('sup-', [status(thm)], ['31', '32'])).
% 6.92/7.13  thf('34', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['18', '24'])).
% 6.92/7.13  thf('35', plain,
% 6.92/7.13      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 6.92/7.13         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 6.92/7.13      inference('clc', [status(thm)], ['33', '34'])).
% 6.92/7.13  thf('36', plain,
% 6.92/7.13      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 6.92/7.13         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 6.92/7.13      inference('clc', [status(thm)], ['33', '34'])).
% 6.92/7.13  thf('37', plain,
% 6.92/7.13      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 6.92/7.13         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 6.92/7.13      inference('demod', [status(thm)], ['30', '35', '36'])).
% 6.92/7.13  thf('38', plain,
% 6.92/7.13      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['9', '14'])).
% 6.92/7.13  thf(l1_zfmisc_1, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 6.92/7.13  thf('39', plain,
% 6.92/7.13      (![X7 : $i, X9 : $i]:
% 6.92/7.13         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 6.92/7.13      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 6.92/7.13  thf('40', plain,
% 6.92/7.13      ((r1_tarski @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 6.92/7.13        (u1_struct_0 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['38', '39'])).
% 6.92/7.13  thf('41', plain,
% 6.92/7.13      (![X13 : $i, X15 : $i]:
% 6.92/7.13         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 6.92/7.13      inference('cnf', [status(esa)], [t3_subset])).
% 6.92/7.13  thf('42', plain,
% 6.92/7.13      ((m1_subset_1 @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 6.92/7.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('sup-', [status(thm)], ['40', '41'])).
% 6.92/7.13  thf(dt_k2_pre_topc, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( ( l1_pre_topc @ A ) & 
% 6.92/7.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.92/7.13       ( m1_subset_1 @
% 6.92/7.13         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.92/7.13  thf('43', plain,
% 6.92/7.13      (![X19 : $i, X20 : $i]:
% 6.92/7.13         (~ (l1_pre_topc @ X19)
% 6.92/7.13          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 6.92/7.13          | (m1_subset_1 @ (k2_pre_topc @ X19 @ X20) @ 
% 6.92/7.13             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 6.92/7.13      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 6.92/7.13  thf('44', plain,
% 6.92/7.13      (((m1_subset_1 @ 
% 6.92/7.13         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 6.92/7.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.92/7.13        | ~ (l1_pre_topc @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['42', '43'])).
% 6.92/7.13  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('46', plain,
% 6.92/7.13      ((m1_subset_1 @ 
% 6.92/7.13        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 6.92/7.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('demod', [status(thm)], ['44', '45'])).
% 6.92/7.13  thf('47', plain,
% 6.92/7.13      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 6.92/7.13         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 6.92/7.13      inference('clc', [status(thm)], ['33', '34'])).
% 6.92/7.13  thf('48', plain,
% 6.92/7.13      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.92/7.13         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 6.92/7.13          | (v2_tex_2 @ X27 @ X28)
% 6.92/7.13          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 6.92/7.13          | ~ (v3_pre_topc @ X29 @ X28)
% 6.92/7.13          | ((k9_subset_1 @ (u1_struct_0 @ X28) @ X27 @ X29)
% 6.92/7.13              != (k6_domain_1 @ (u1_struct_0 @ X28) @ (sk_C_1 @ X27 @ X28)))
% 6.92/7.13          | ~ (l1_pre_topc @ X28)
% 6.92/7.13          | ~ (v2_pre_topc @ X28)
% 6.92/7.13          | (v2_struct_0 @ X28))),
% 6.92/7.13      inference('cnf', [status(esa)], [t37_tex_2])).
% 6.92/7.13  thf('49', plain,
% 6.92/7.13      (![X0 : $i]:
% 6.92/7.13         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 6.92/7.13            != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 6.92/7.13          | (v2_struct_0 @ sk_A)
% 6.92/7.13          | ~ (v2_pre_topc @ sk_A)
% 6.92/7.13          | ~ (l1_pre_topc @ sk_A)
% 6.92/7.13          | ~ (v3_pre_topc @ X0 @ sk_A)
% 6.92/7.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.92/7.13          | (v2_tex_2 @ sk_B_1 @ sk_A)
% 6.92/7.13          | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.92/7.13      inference('sup-', [status(thm)], ['47', '48'])).
% 6.92/7.13  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('52', plain,
% 6.92/7.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('53', plain,
% 6.92/7.13      (![X0 : $i]:
% 6.92/7.13         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 6.92/7.13            != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 6.92/7.13          | (v2_struct_0 @ sk_A)
% 6.92/7.13          | ~ (v3_pre_topc @ X0 @ sk_A)
% 6.92/7.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.92/7.13          | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 6.92/7.13      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 6.92/7.13  thf('54', plain,
% 6.92/7.13      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 6.92/7.13        | ~ (v3_pre_topc @ 
% 6.92/7.13             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 6.92/7.13             sk_A)
% 6.92/7.13        | (v2_struct_0 @ sk_A)
% 6.92/7.13        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13            (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 6.92/7.13            != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 6.92/7.13      inference('sup-', [status(thm)], ['46', '53'])).
% 6.92/7.13  thf('55', plain,
% 6.92/7.13      ((m1_subset_1 @ 
% 6.92/7.13        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 6.92/7.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('demod', [status(thm)], ['44', '45'])).
% 6.92/7.13  thf(t24_tdlat_3, axiom,
% 6.92/7.13    (![A:$i]:
% 6.92/7.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.92/7.13       ( ( v3_tdlat_3 @ A ) <=>
% 6.92/7.13         ( ![B:$i]:
% 6.92/7.13           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.92/7.13             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 6.92/7.13  thf('56', plain,
% 6.92/7.13      (![X25 : $i, X26 : $i]:
% 6.92/7.13         (~ (v3_tdlat_3 @ X25)
% 6.92/7.13          | ~ (v4_pre_topc @ X26 @ X25)
% 6.92/7.13          | (v3_pre_topc @ X26 @ X25)
% 6.92/7.13          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 6.92/7.13          | ~ (l1_pre_topc @ X25)
% 6.92/7.13          | ~ (v2_pre_topc @ X25))),
% 6.92/7.13      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 6.92/7.13  thf('57', plain,
% 6.92/7.13      ((~ (v2_pre_topc @ sk_A)
% 6.92/7.13        | ~ (l1_pre_topc @ sk_A)
% 6.92/7.13        | (v3_pre_topc @ 
% 6.92/7.13           (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)
% 6.92/7.13        | ~ (v4_pre_topc @ 
% 6.92/7.13             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 6.92/7.13             sk_A)
% 6.92/7.13        | ~ (v3_tdlat_3 @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['55', '56'])).
% 6.92/7.13  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('60', plain,
% 6.92/7.13      ((m1_subset_1 @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 6.92/7.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.92/7.13      inference('sup-', [status(thm)], ['40', '41'])).
% 6.92/7.13  thf(fc1_tops_1, axiom,
% 6.92/7.13    (![A:$i,B:$i]:
% 6.92/7.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 6.92/7.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.92/7.13       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 6.92/7.13  thf('61', plain,
% 6.92/7.13      (![X23 : $i, X24 : $i]:
% 6.92/7.13         (~ (l1_pre_topc @ X23)
% 6.92/7.13          | ~ (v2_pre_topc @ X23)
% 6.92/7.13          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 6.92/7.13          | (v4_pre_topc @ (k2_pre_topc @ X23 @ X24) @ X23))),
% 6.92/7.13      inference('cnf', [status(esa)], [fc1_tops_1])).
% 6.92/7.13  thf('62', plain,
% 6.92/7.13      (((v4_pre_topc @ 
% 6.92/7.13         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)
% 6.92/7.13        | ~ (v2_pre_topc @ sk_A)
% 6.92/7.13        | ~ (l1_pre_topc @ sk_A))),
% 6.92/7.13      inference('sup-', [status(thm)], ['60', '61'])).
% 6.92/7.13  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('65', plain,
% 6.92/7.13      ((v4_pre_topc @ 
% 6.92/7.13        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)),
% 6.92/7.13      inference('demod', [status(thm)], ['62', '63', '64'])).
% 6.92/7.13  thf('66', plain, ((v3_tdlat_3 @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('67', plain,
% 6.92/7.13      ((v3_pre_topc @ 
% 6.92/7.13        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)),
% 6.92/7.13      inference('demod', [status(thm)], ['57', '58', '59', '65', '66'])).
% 6.92/7.13  thf('68', plain,
% 6.92/7.13      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 6.92/7.13        | (v2_struct_0 @ sk_A)
% 6.92/7.13        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13            (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 6.92/7.13            != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 6.92/7.13      inference('demod', [status(thm)], ['54', '67'])).
% 6.92/7.13  thf('69', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('70', plain,
% 6.92/7.13      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13          (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 6.92/7.13          != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 6.92/7.13        | (v2_struct_0 @ sk_A))),
% 6.92/7.13      inference('clc', [status(thm)], ['68', '69'])).
% 6.92/7.13  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 6.92/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.92/7.13  thf('72', plain,
% 6.92/7.13      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 6.92/7.13         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 6.92/7.13         != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 6.92/7.13      inference('clc', [status(thm)], ['70', '71'])).
% 6.92/7.13  thf('73', plain, ($false),
% 6.92/7.13      inference('simplify_reflect-', [status(thm)], ['37', '72'])).
% 6.92/7.13  
% 6.92/7.13  % SZS output end Refutation
% 6.92/7.13  
% 6.96/7.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
