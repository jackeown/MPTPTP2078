%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ySsrFwgr83

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 497 expanded)
%              Number of leaves         :   32 ( 160 expanded)
%              Depth                    :   17
%              Number of atoms          :  813 (8709 expanded)
%              Number of equality atoms :   15 ( 186 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X24 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('18',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X26 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('23',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','33'])).

thf('35',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','33'])).

thf('36',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('37',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','34','35','36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ ( sk_C_1 @ X23 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('39',plain,
    ( ( ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','33'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('45',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v4_pre_topc @ X22 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('53',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('58',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['53','54','55','61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
     != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42','63','64','65'])).

thf('67',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ySsrFwgr83
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 180 iterations in 0.109s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(t58_tex_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.56         ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56                 ( ( r2_hidden @ C @ B ) =>
% 0.20/0.56                   ( ( k9_subset_1 @
% 0.20/0.56                       ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.56                       ( k2_pre_topc @
% 0.20/0.56                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.56                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.20/0.56             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ( ![C:$i]:
% 0.20/0.56                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56                    ( ( r2_hidden @ C @ B ) =>
% 0.20/0.56                      ( ( k9_subset_1 @
% 0.20/0.56                          ( u1_struct_0 @ A ) @ B @ 
% 0.20/0.56                          ( k2_pre_topc @
% 0.20/0.56                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.20/0.56                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.20/0.56                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.20/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t37_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.56                      ( ![D:$i]:
% 0.20/0.56                        ( ( m1_subset_1 @
% 0.20/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.56                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.56                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.56             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X23 : $i, X24 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.56          | (v2_tex_2 @ X23 @ X24)
% 0.20/0.56          | (r2_hidden @ (sk_C_1 @ X23 @ X24) @ X23)
% 0.20/0.56          | ~ (l1_pre_topc @ X24)
% 0.20/0.56          | ~ (v2_pre_topc @ X24)
% 0.20/0.56          | (v2_struct_0 @ X24))),
% 0.20/0.56      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.20/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.20/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.56  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.56        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.20/0.56      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf('9', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('10', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.20/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t3_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.56  thf('13', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf(d3_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.56          | (r2_hidden @ X0 @ X2)
% 0.20/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.56  thf(t1_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X26 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X26 @ sk_B_1)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.20/0.56              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X26)))
% 0.20/0.56              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X26))
% 0.20/0.56          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.20/0.56          (k2_pre_topc @ sk_A @ 
% 0.20/0.56           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.20/0.56          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.56        | ~ (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X17 : $i, X18 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X17)
% 0.20/0.56          | ~ (m1_subset_1 @ X18 @ X17)
% 0.20/0.56          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.56          = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X1 : $i, X3 : $i]:
% 0.20/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X1 : $i, X3 : $i]:
% 0.20/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('28', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X9 : $i, X11 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.56  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf(t5_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X12 @ X13)
% 0.20/0.56          | ~ (v1_xboole_0 @ X14)
% 0.20/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('33', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '32'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.56         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['23', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.56         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['23', '33'])).
% 0.20/0.56  thf('36', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.20/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.20/0.56         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.20/0.56         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['20', '34', '35', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.56          | (v2_tex_2 @ X23 @ X24)
% 0.20/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.20/0.56          | ~ (v3_pre_topc @ X25 @ X24)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X25)
% 0.20/0.56              != (k6_domain_1 @ (u1_struct_0 @ X24) @ (sk_C_1 @ X23 @ X24)))
% 0.20/0.56          | ~ (l1_pre_topc @ X24)
% 0.20/0.56          | ~ (v2_pre_topc @ X24)
% 0.20/0.56          | (v2_struct_0 @ X24))),
% 0.20/0.56      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((((k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.56          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.56        | (v2_struct_0 @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v3_pre_topc @ 
% 0.20/0.56             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.20/0.56             sk_A)
% 0.20/0.56        | ~ (m1_subset_1 @ 
% 0.20/0.56             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.56        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.56         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['23', '33'])).
% 0.20/0.56  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.56  thf(l1_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X4 : $i, X6 : $i]:
% 0.20/0.56         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((r1_tarski @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.56        (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X9 : $i, X11 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      ((m1_subset_1 @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf(dt_k2_pre_topc, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56       ( m1_subset_1 @
% 0.20/0.56         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X15)
% 0.20/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.56          | (m1_subset_1 @ (k2_pre_topc @ X15 @ X16) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (((m1_subset_1 @ 
% 0.20/0.56         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.20/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      ((m1_subset_1 @ 
% 0.20/0.56        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf(t24_tdlat_3, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.56         ( ![B:$i]:
% 0.20/0.56           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i]:
% 0.20/0.56         (~ (v3_tdlat_3 @ X21)
% 0.20/0.56          | ~ (v4_pre_topc @ X22 @ X21)
% 0.20/0.56          | (v3_pre_topc @ X22 @ X21)
% 0.20/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.56          | ~ (l1_pre_topc @ X21)
% 0.20/0.56          | ~ (v2_pre_topc @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_pre_topc @ 
% 0.20/0.56           (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)
% 0.20/0.56        | ~ (v4_pre_topc @ 
% 0.20/0.56             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.20/0.56             sk_A)
% 0.20/0.56        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.56  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      ((m1_subset_1 @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf(fc1_tops_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X19)
% 0.20/0.56          | ~ (v2_pre_topc @ X19)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.56          | (v4_pre_topc @ (k2_pre_topc @ X19 @ X20) @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (((v4_pre_topc @ 
% 0.20/0.56         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      ((v4_pre_topc @ 
% 0.20/0.56        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.56  thf('62', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      ((v3_pre_topc @ 
% 0.20/0.56        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['53', '54', '55', '61', '62'])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      ((m1_subset_1 @ 
% 0.20/0.56        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('66', plain,
% 0.20/0.56      ((((k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.56          != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.56        | (v2_struct_0 @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)],
% 0.20/0.56                ['39', '40', '41', '42', '63', '64', '65'])).
% 0.20/0.56  thf('67', plain, (((v2_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('simplify', [status(thm)], ['66'])).
% 0.20/0.56  thf('68', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('69', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['67', '68'])).
% 0.20/0.56  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
