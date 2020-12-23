%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t4lH1ZLqwF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:31 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 463 expanded)
%              Number of leaves         :   35 ( 148 expanded)
%              Depth                    :   16
%              Number of atoms          :  982 (8498 expanded)
%              Number of equality atoms :   29 ( 207 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tex_2 @ X32 @ X33 )
      | ( r2_hidden @ ( sk_C_1 @ X32 @ X33 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X35 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X7 @ X9 @ X8 )
        = ( k9_subset_1 @ X7 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_1 )
      = ( k3_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B_1 )
      | ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X35 ) ) @ sk_B_1 )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X35: $i] :
      ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X35 ) ) @ sk_B_1 )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X35 ) )
      | ~ ( r2_hidden @ X35 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_B_1 )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('29',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','43'])).

thf('45',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','43'])).

thf('46',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_B_1 )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','44','45'])).

thf('47',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','43'])).

thf('48',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tex_2 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X33 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ X34 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ ( sk_C_1 @ X32 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B_1 )
       != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
     != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('58',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('59',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v3_tdlat_3 @ X30 )
      | ~ ( v4_pre_topc @ X31 @ X30 )
      | ( v3_pre_topc @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('69',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('70',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['65','66','67','73','74'])).

thf('76',plain,
    ( ( ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
     != ( k1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','62','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t4lH1ZLqwF
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:46:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 409 iterations in 0.445s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.68/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.88  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.68/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.88  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.68/0.88  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(t58_tex_2, conjecture,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.68/0.88         ( l1_pre_topc @ A ) ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( ( ![C:$i]:
% 0.68/0.88               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88                 ( ( r2_hidden @ C @ B ) =>
% 0.68/0.88                   ( ( k9_subset_1 @
% 0.68/0.88                       ( u1_struct_0 @ A ) @ B @ 
% 0.68/0.88                       ( k2_pre_topc @
% 0.68/0.88                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.68/0.88                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.68/0.88             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i]:
% 0.68/0.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.88            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.88          ( ![B:$i]:
% 0.68/0.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88              ( ( ![C:$i]:
% 0.68/0.88                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88                    ( ( r2_hidden @ C @ B ) =>
% 0.68/0.88                      ( ( k9_subset_1 @
% 0.68/0.88                          ( u1_struct_0 @ A ) @ B @ 
% 0.68/0.88                          ( k2_pre_topc @
% 0.68/0.88                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.68/0.88                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.68/0.88                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.68/0.88  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t37_tex_2, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( ( ![C:$i]:
% 0.68/0.88               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.68/0.88                      ( ![D:$i]:
% 0.68/0.88                        ( ( m1_subset_1 @
% 0.68/0.88                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.68/0.88                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.68/0.88                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.68/0.88             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X32 : $i, X33 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.68/0.88          | (v2_tex_2 @ X32 @ X33)
% 0.68/0.88          | (r2_hidden @ (sk_C_1 @ X32 @ X33) @ X32)
% 0.68/0.88          | ~ (l1_pre_topc @ X33)
% 0.68/0.88          | ~ (v2_pre_topc @ X33)
% 0.68/0.88          | (v2_struct_0 @ X33))),
% 0.68/0.88      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (((v2_struct_0 @ sk_A)
% 0.68/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.68/0.88        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (((v2_struct_0 @ sk_A)
% 0.68/0.88        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.68/0.88        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.68/0.88  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.68/0.88        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.68/0.88      inference('clc', [status(thm)], ['6', '7'])).
% 0.68/0.88  thf('9', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('10', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.68/0.88      inference('clc', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X35 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X35 @ sk_B_1)
% 0.68/0.88          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.68/0.88              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X35)))
% 0.68/0.88              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X35))
% 0.68/0.88          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(commutativity_k9_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.88         (((k9_subset_1 @ X7 @ X9 @ X8) = (k9_subset_1 @ X7 @ X8 @ X9))
% 0.68/0.88          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B_1)
% 0.68/0.88           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k9_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.88         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.68/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B_1)
% 0.68/0.88           = (k3_xboole_0 @ X0 @ sk_B_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X0 @ sk_B_1)
% 0.68/0.88           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X35 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X35 @ sk_B_1)
% 0.68/0.88          | ((k3_xboole_0 @ 
% 0.68/0.88              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X35)) @ 
% 0.68/0.88              sk_B_1) = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X35))
% 0.68/0.88          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['11', '18'])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t4_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.68/0.88       ( m1_subset_1 @ A @ C ) ))).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X18 @ X19)
% 0.68/0.88          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.68/0.88          | (m1_subset_1 @ X18 @ X20))),
% 0.68/0.88      inference('cnf', [status(esa)], [t4_subset])).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X35 : $i]:
% 0.68/0.88         (((k3_xboole_0 @ 
% 0.68/0.88            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X35)) @ 
% 0.68/0.88            sk_B_1) = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X35))
% 0.68/0.88          | ~ (r2_hidden @ X35 @ sk_B_1))),
% 0.68/0.88      inference('clc', [status(thm)], ['19', '22'])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (((k3_xboole_0 @ 
% 0.68/0.88         (k2_pre_topc @ sk_A @ 
% 0.68/0.88          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.68/0.88         sk_B_1)
% 0.68/0.88         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['10', '23'])).
% 0.68/0.88  thf('25', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.68/0.88      inference('clc', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.88  thf(redefinition_k6_domain_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.68/0.88       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X26 : $i, X27 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ X26)
% 0.68/0.88          | ~ (m1_subset_1 @ X27 @ X26)
% 0.68/0.88          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.68/0.88          = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.88  thf('30', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.68/0.88      inference('clc', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t3_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]:
% 0.68/0.88         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.88  thf('33', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['31', '32'])).
% 0.68/0.88  thf(d3_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.88          | (r2_hidden @ X0 @ X2)
% 0.68/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['30', '35'])).
% 0.68/0.88  thf(d10_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('38', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.68/0.88      inference('simplify', [status(thm)], ['37'])).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (![X15 : $i, X17 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.88  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['38', '39'])).
% 0.68/0.88  thf(t5_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.68/0.88          ( v1_xboole_0 @ C ) ) ))).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X21 @ X22)
% 0.68/0.88          | ~ (v1_xboole_0 @ X23)
% 0.68/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t5_subset])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['40', '41'])).
% 0.68/0.88  thf('43', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['36', '42'])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.68/0.88         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('clc', [status(thm)], ['29', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.68/0.88         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('clc', [status(thm)], ['29', '43'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (((k3_xboole_0 @ 
% 0.68/0.88         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_B_1)
% 0.68/0.88         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['24', '44', '45'])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.68/0.88         = (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('clc', [status(thm)], ['29', '43'])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.68/0.88          | (v2_tex_2 @ X32 @ X33)
% 0.68/0.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.68/0.88          | ~ (v3_pre_topc @ X34 @ X33)
% 0.68/0.88          | ((k9_subset_1 @ (u1_struct_0 @ X33) @ X32 @ X34)
% 0.68/0.88              != (k6_domain_1 @ (u1_struct_0 @ X33) @ (sk_C_1 @ X32 @ X33)))
% 0.68/0.88          | ~ (l1_pre_topc @ X33)
% 0.68/0.88          | ~ (v2_pre_topc @ X33)
% 0.68/0.88          | (v2_struct_0 @ X33))),
% 0.68/0.88      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 0.68/0.88            != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.68/0.88          | (v2_struct_0 @ sk_A)
% 0.68/0.88          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.88          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.88          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88          | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.68/0.88          | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['47', '48'])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X0 @ sk_B_1)
% 0.68/0.88           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17'])).
% 0.68/0.88  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((k3_xboole_0 @ X0 @ sk_B_1)
% 0.68/0.88            != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.68/0.88          | (v2_struct_0 @ sk_A)
% 0.68/0.88          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88          | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      ((((k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.68/0.88          != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.68/0.88        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ~ (m1_subset_1 @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.68/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88        | ~ (v3_pre_topc @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.68/0.88             sk_A)
% 0.68/0.88        | (v2_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['46', '54'])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['30', '35'])).
% 0.68/0.88  thf(t63_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r2_hidden @ A @ B ) =>
% 0.68/0.88       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (![X13 : $i, X14 : $i]:
% 0.68/0.88         ((m1_subset_1 @ (k1_tarski @ X13) @ (k1_zfmisc_1 @ X14))
% 0.68/0.88          | ~ (r2_hidden @ X13 @ X14))),
% 0.68/0.88      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      ((m1_subset_1 @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['56', '57'])).
% 0.68/0.88  thf(dt_k2_pre_topc, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( l1_pre_topc @ A ) & 
% 0.68/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88       ( m1_subset_1 @
% 0.68/0.88         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (![X24 : $i, X25 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X24)
% 0.68/0.88          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.68/0.88          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 0.68/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (((m1_subset_1 @ 
% 0.68/0.88         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.88  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      ((m1_subset_1 @ 
% 0.68/0.88        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      ((m1_subset_1 @ 
% 0.68/0.88        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf(t24_tdlat_3, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.88       ( ( v3_tdlat_3 @ A ) <=>
% 0.68/0.88         ( ![B:$i]:
% 0.68/0.88           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (![X30 : $i, X31 : $i]:
% 0.68/0.88         (~ (v3_tdlat_3 @ X30)
% 0.68/0.88          | ~ (v4_pre_topc @ X31 @ X30)
% 0.68/0.88          | (v3_pre_topc @ X31 @ X30)
% 0.68/0.88          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.68/0.88          | ~ (l1_pre_topc @ X30)
% 0.68/0.88          | ~ (v2_pre_topc @ X30))),
% 0.68/0.88      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      ((~ (v2_pre_topc @ sk_A)
% 0.68/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | (v3_pre_topc @ 
% 0.68/0.88           (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)
% 0.68/0.88        | ~ (v4_pre_topc @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.68/0.88             sk_A)
% 0.68/0.88        | ~ (v3_tdlat_3 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['63', '64'])).
% 0.68/0.88  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('68', plain,
% 0.68/0.88      ((m1_subset_1 @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['56', '57'])).
% 0.68/0.88  thf(fc1_tops_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.68/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X28 : $i, X29 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X28)
% 0.68/0.88          | ~ (v2_pre_topc @ X28)
% 0.68/0.88          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.68/0.88          | (v4_pre_topc @ (k2_pre_topc @ X28 @ X29) @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      (((v4_pre_topc @ 
% 0.68/0.88         (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)
% 0.68/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['68', '69'])).
% 0.68/0.88  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      ((v4_pre_topc @ 
% 0.68/0.88        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.68/0.88  thf('74', plain, ((v3_tdlat_3 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      ((v3_pre_topc @ 
% 0.68/0.88        (k2_pre_topc @ sk_A @ (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))) @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['65', '66', '67', '73', '74'])).
% 0.68/0.88  thf('76', plain,
% 0.68/0.88      ((((k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.68/0.88          != (k1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.68/0.88        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.68/0.88        | (v2_struct_0 @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['55', '62', '75'])).
% 0.68/0.88  thf('77', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('simplify', [status(thm)], ['76'])).
% 0.68/0.88  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('79', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.68/0.88      inference('clc', [status(thm)], ['77', '78'])).
% 0.68/0.88  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
