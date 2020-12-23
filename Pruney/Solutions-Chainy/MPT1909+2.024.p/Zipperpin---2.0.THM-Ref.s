%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQEk0d95WZ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 474 expanded)
%              Number of leaves         :   39 ( 157 expanded)
%              Depth                    :   26
%              Number of atoms          : 1252 (11937 expanded)
%              Number of equality atoms :   30 ( 305 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t77_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                            = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_borsuk_1 @ C @ A @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( D = E )
                           => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                              = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v4_tex_2 @ X22 @ X23 )
      | ( X24
       != ( u1_struct_0 @ X22 ) )
      | ( v3_tex_2 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X22 ) @ X23 )
      | ~ ( v4_tex_2 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','15','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('44',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('47',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_D ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_D ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tarski @ ( k1_tarski @ sk_D ) @ X0 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t76_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                            = ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_tex_2 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v3_borsuk_1 @ X29 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( X30 != X31 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) @ X29 @ X30 )
        = ( k2_pre_topc @ X28 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v5_pre_topc @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v3_tdlat_3 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('70',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( v3_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ X29 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) @ X29 @ X31 )
        = ( k2_pre_topc @ X28 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_borsuk_1 @ X29 @ X28 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v4_tex_2 @ X27 @ X28 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77','78','79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('85',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('91',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_2 @ ( k1_tarski @ sk_D ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('99',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','99'])).

thf('101',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['28','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQEk0d95WZ
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 381 iterations in 0.205s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.67  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.67  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.67  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.67  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.67  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.67  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(t77_tex_2, conjecture,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.67         ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.67             ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.67           ( ![C:$i]:
% 0.46/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.67                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.67                 ( m1_subset_1 @
% 0.46/0.67                   C @ 
% 0.46/0.67                   ( k1_zfmisc_1 @
% 0.46/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.67               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.67                 ( ![D:$i]:
% 0.46/0.67                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.67                     ( ![E:$i]:
% 0.46/0.67                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.67                         ( ( ( D ) = ( E ) ) =>
% 0.46/0.67                           ( ( k8_relset_1 @
% 0.46/0.67                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.67                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.46/0.67                             ( k2_pre_topc @
% 0.46/0.67                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i]:
% 0.46/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.67            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67          ( ![B:$i]:
% 0.46/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.67                ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.67              ( ![C:$i]:
% 0.46/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.67                    ( v1_funct_2 @
% 0.46/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.67                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.67                    ( m1_subset_1 @
% 0.46/0.67                      C @ 
% 0.46/0.67                      ( k1_zfmisc_1 @
% 0.46/0.67                        ( k2_zfmisc_1 @
% 0.46/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.67                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.67                    ( ![D:$i]:
% 0.46/0.67                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.67                        ( ![E:$i]:
% 0.46/0.67                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.67                            ( ( ( D ) = ( E ) ) =>
% 0.46/0.67                              ( ( k8_relset_1 @
% 0.46/0.67                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.67                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.46/0.67                                ( k2_pre_topc @
% 0.46/0.67                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.46/0.67  thf('0', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d3_tarski, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X4 : $i, X6 : $i]:
% 0.46/0.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X4 : $i, X6 : $i]:
% 0.46/0.67         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.67  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.67      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.67  thf(t3_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X12 : $i, X14 : $i]:
% 0.46/0.67         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('6', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf(t39_pre_topc, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.67           ( ![C:$i]:
% 0.46/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.67               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.67         (~ (m1_pre_topc @ X15 @ X16)
% 0.46/0.67          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.67          | ~ (l1_pre_topc @ X16))),
% 0.46/0.67      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X1)
% 0.46/0.67          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.46/0.67          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '8'])).
% 0.46/0.67  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.67  thf(t46_tex_2, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.67             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.67           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X25)
% 0.46/0.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.46/0.67          | ~ (v3_tex_2 @ X25 @ X26)
% 0.46/0.67          | ~ (l1_pre_topc @ X26)
% 0.46/0.67          | ~ (v2_pre_topc @ X26)
% 0.46/0.67          | (v2_struct_0 @ X26))),
% 0.46/0.67      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (((v2_struct_0 @ sk_A)
% 0.46/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.67        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.46/0.67        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.67  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.67  thf(d8_tex_2, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.67           ( ( v4_tex_2 @ B @ A ) <=>
% 0.46/0.67             ( ![C:$i]:
% 0.46/0.67               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.67         (~ (m1_pre_topc @ X22 @ X23)
% 0.46/0.67          | ~ (v4_tex_2 @ X22 @ X23)
% 0.46/0.67          | ((X24) != (u1_struct_0 @ X22))
% 0.46/0.67          | (v3_tex_2 @ X24 @ X23)
% 0.46/0.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.67          | ~ (l1_pre_topc @ X23)
% 0.46/0.67          | (v2_struct_0 @ X23))),
% 0.46/0.67      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X22 : $i, X23 : $i]:
% 0.46/0.67         ((v2_struct_0 @ X23)
% 0.46/0.67          | ~ (l1_pre_topc @ X23)
% 0.46/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.46/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.67          | (v3_tex_2 @ (u1_struct_0 @ X22) @ X23)
% 0.46/0.67          | ~ (v4_tex_2 @ X22 @ X23)
% 0.46/0.67          | ~ (m1_pre_topc @ X22 @ X23))),
% 0.46/0.67      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.46/0.67        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.67        | (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.46/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.67        | (v2_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['16', '18'])).
% 0.46/0.67  thf('20', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('21', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.46/0.67  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('25', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.46/0.67      inference('clc', [status(thm)], ['23', '24'])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (((v2_struct_0 @ sk_A) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('demod', [status(thm)], ['13', '14', '15', '25'])).
% 0.46/0.67  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('28', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('clc', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('29', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t2_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X10 : $i, X11 : $i]:
% 0.46/0.67         ((r2_hidden @ X10 @ X11)
% 0.46/0.67          | (v1_xboole_0 @ X11)
% 0.46/0.67          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i]:
% 0.46/0.67         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.67          | (r2_hidden @ X3 @ X5)
% 0.46/0.67          | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.67          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '36'])).
% 0.46/0.67  thf(d1_xboole_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf('40', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('41', plain, (((sk_D) = (sk_E))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('42', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.67  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.67       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X18 : $i, X19 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ X18)
% 0.46/0.67          | ~ (m1_subset_1 @ X19 @ X18)
% 0.46/0.67          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.67  thf('45', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X18 : $i, X19 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ X18)
% 0.46/0.67          | ~ (m1_subset_1 @ X19 @ X18)
% 0.46/0.67          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.46/0.67         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('49', plain, (((sk_D) = (sk_E))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('50', plain,
% 0.46/0.67      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67         sk_C_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.46/0.67         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.46/0.67      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.67  thf('51', plain,
% 0.46/0.67      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67          sk_C_2 @ (k1_tarski @ sk_D))
% 0.46/0.67          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.46/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['47', '50'])).
% 0.46/0.67  thf('52', plain,
% 0.46/0.67      (![X4 : $i, X6 : $i]:
% 0.46/0.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.67  thf(t63_subset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.67       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X8 : $i, X9 : $i]:
% 0.46/0.67         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.46/0.67          | ~ (r2_hidden @ X8 @ X9))),
% 0.46/0.67      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.46/0.67  thf('55', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      (![X12 : $i, X13 : $i]:
% 0.46/0.67         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('57', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.67  thf('58', plain,
% 0.46/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.67          | (r2_hidden @ X3 @ X5)
% 0.46/0.67          | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_D)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.67  thf('60', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((r1_tarski @ (k1_tarski @ sk_D) @ X0)
% 0.46/0.67          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_D)) @ 
% 0.46/0.67             (u1_struct_0 @ sk_B_1))
% 0.46/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['52', '59'])).
% 0.46/0.67  thf('61', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('clc', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('62', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_D)) @ 
% 0.46/0.67           (u1_struct_0 @ sk_B_1))
% 0.46/0.67          | (r1_tarski @ (k1_tarski @ sk_D) @ X0))),
% 0.46/0.67      inference('clc', [status(thm)], ['60', '61'])).
% 0.46/0.67  thf('63', plain,
% 0.46/0.67      (![X4 : $i, X6 : $i]:
% 0.46/0.67         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.67  thf('64', plain,
% 0.46/0.67      (((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | (r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.67  thf('65', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.67  thf('66', plain,
% 0.46/0.67      (![X12 : $i, X14 : $i]:
% 0.46/0.67         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('67', plain,
% 0.46/0.67      ((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_C_2 @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t76_tex_2, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.67         ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.67             ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.67           ( ![C:$i]:
% 0.46/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.67                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.67                 ( m1_subset_1 @
% 0.46/0.67                   C @ 
% 0.46/0.67                   ( k1_zfmisc_1 @
% 0.46/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.67               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.67                 ( ![D:$i]:
% 0.46/0.67                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.67                     ( ![E:$i]:
% 0.46/0.67                       ( ( m1_subset_1 @
% 0.46/0.67                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.67                         ( ( ( D ) = ( E ) ) =>
% 0.46/0.67                           ( ( k8_relset_1 @
% 0.46/0.67                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.67                               D ) =
% 0.46/0.67                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf('69', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.67         ((v2_struct_0 @ X27)
% 0.46/0.67          | ~ (v4_tex_2 @ X27 @ X28)
% 0.46/0.67          | ~ (m1_pre_topc @ X27 @ X28)
% 0.46/0.67          | ~ (v3_borsuk_1 @ X29 @ X28 @ X27)
% 0.46/0.67          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.67          | ((X30) != (X31))
% 0.46/0.67          | ((k8_relset_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27) @ X29 @ 
% 0.46/0.67              X30) = (k2_pre_topc @ X28 @ X31))
% 0.46/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ 
% 0.46/0.67               (k1_zfmisc_1 @ 
% 0.46/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.46/0.67          | ~ (v5_pre_topc @ X29 @ X28 @ X27)
% 0.46/0.67          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.46/0.67          | ~ (v1_funct_1 @ X29)
% 0.46/0.67          | ~ (l1_pre_topc @ X28)
% 0.46/0.67          | ~ (v3_tdlat_3 @ X28)
% 0.46/0.67          | ~ (v2_pre_topc @ X28)
% 0.46/0.67          | (v2_struct_0 @ X28))),
% 0.46/0.67      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.46/0.67         ((v2_struct_0 @ X28)
% 0.46/0.67          | ~ (v2_pre_topc @ X28)
% 0.46/0.67          | ~ (v3_tdlat_3 @ X28)
% 0.46/0.67          | ~ (l1_pre_topc @ X28)
% 0.46/0.67          | ~ (v1_funct_1 @ X29)
% 0.46/0.67          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.46/0.67          | ~ (v5_pre_topc @ X29 @ X28 @ X27)
% 0.46/0.67          | ~ (m1_subset_1 @ X29 @ 
% 0.46/0.67               (k1_zfmisc_1 @ 
% 0.46/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.46/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.46/0.67          | ((k8_relset_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27) @ X29 @ 
% 0.46/0.67              X31) = (k2_pre_topc @ X28 @ X31))
% 0.46/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.67          | ~ (v3_borsuk_1 @ X29 @ X28 @ X27)
% 0.46/0.67          | ~ (m1_pre_topc @ X27 @ X28)
% 0.46/0.67          | ~ (v4_tex_2 @ X27 @ X28)
% 0.46/0.67          | (v2_struct_0 @ X27))),
% 0.46/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.46/0.67  thf('71', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v2_struct_0 @ sk_B_1)
% 0.46/0.67          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.67          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.46/0.67          | ~ (v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.46/0.67          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67              sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67          | ~ (v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)
% 0.46/0.67          | ~ (v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.67               (u1_struct_0 @ sk_B_1))
% 0.46/0.67          | ~ (v1_funct_1 @ sk_C_2)
% 0.46/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.67          | ~ (v3_tdlat_3 @ sk_A)
% 0.46/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.67          | (v2_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['68', '70'])).
% 0.46/0.67  thf('72', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('73', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('74', plain, ((v3_borsuk_1 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('75', plain, ((v5_pre_topc @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('76', plain,
% 0.46/0.67      ((v1_funct_2 @ sk_C_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('77', plain, ((v1_funct_1 @ sk_C_2)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('79', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('81', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v2_struct_0 @ sk_B_1)
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.46/0.67          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67              sk_C_2 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.46/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67          | (v2_struct_0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)],
% 0.46/0.67                ['71', '72', '73', '74', '75', '76', '77', '78', '79', '80'])).
% 0.46/0.67  thf('82', plain,
% 0.46/0.67      (((v2_struct_0 @ sk_A)
% 0.46/0.67        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67            sk_C_2 @ (k1_tarski @ sk_D))
% 0.46/0.67            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.67        | (v2_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['67', '81'])).
% 0.46/0.67  thf('83', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('84', plain,
% 0.46/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.67  thf('85', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.67         (~ (m1_pre_topc @ X15 @ X16)
% 0.46/0.67          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.67          | ~ (l1_pre_topc @ X16))),
% 0.46/0.67      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.46/0.67  thf('86', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.46/0.67          | ~ (l1_pre_topc @ X0)
% 0.46/0.67          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.67          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['84', '85'])).
% 0.46/0.67  thf('87', plain,
% 0.46/0.67      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['83', '86'])).
% 0.46/0.67  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('89', plain,
% 0.46/0.67      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('demod', [status(thm)], ['87', '88'])).
% 0.46/0.67  thf('90', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('clc', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('91', plain,
% 0.46/0.67      ((m1_subset_1 @ (k1_tarski @ sk_D) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('clc', [status(thm)], ['89', '90'])).
% 0.46/0.67  thf('92', plain,
% 0.46/0.67      (((v2_struct_0 @ sk_A)
% 0.46/0.67        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67            sk_C_2 @ (k1_tarski @ sk_D))
% 0.46/0.67            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.67        | (v2_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['82', '91'])).
% 0.46/0.67  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('94', plain,
% 0.46/0.67      (((v2_struct_0 @ sk_B_1)
% 0.46/0.67        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67            sk_C_2 @ (k1_tarski @ sk_D))
% 0.46/0.67            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.46/0.67      inference('clc', [status(thm)], ['92', '93'])).
% 0.46/0.67  thf('95', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('96', plain,
% 0.46/0.67      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.67         sk_C_2 @ (k1_tarski @ sk_D))
% 0.46/0.67         = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))),
% 0.46/0.67      inference('clc', [status(thm)], ['94', '95'])).
% 0.46/0.67  thf('97', plain,
% 0.46/0.67      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.67          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.46/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.46/0.67      inference('demod', [status(thm)], ['51', '96'])).
% 0.46/0.67  thf('98', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('clc', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('99', plain,
% 0.46/0.67      (((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.67         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.46/0.67      inference('clc', [status(thm)], ['97', '98'])).
% 0.46/0.67  thf('100', plain,
% 0.46/0.67      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.67          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['44', '99'])).
% 0.46/0.67  thf('101', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.67      inference('simplify', [status(thm)], ['100'])).
% 0.46/0.67  thf('102', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['39', '101'])).
% 0.46/0.67  thf('103', plain, ($false), inference('demod', [status(thm)], ['28', '102'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
