%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1859+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IoSA3qqxgo

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:26 EST 2020

% Result     : Theorem 12.63s
% Output     : Refutation 12.63s
% Verified   : 
% Statistics : Number of formulae       :  320 (3123 expanded)
%              Number of leaves         :   36 ( 990 expanded)
%              Depth                    :   33
%              Number of atoms          : 2737 (26956 expanded)
%              Number of equality atoms :  159 (1889 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t27_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( B
                = ( u1_struct_0 @ A ) )
             => ( ( v2_tex_2 @ B @ A )
              <=> ( v1_tdlat_3 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tex_2])).

thf('0',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
   <= ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('8',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X13 @ X14 ) @ X13 )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X13 @ X14 ) @ X13 )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( ( k3_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      = ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('26',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X17 @ X18 @ X19 ) @ ( k9_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('31',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( ~ ( v1_tdlat_3 @ X6 )
      | ( ( u1_pre_topc @ X6 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ X16 )
       != ( sk_C_1 @ X13 @ X14 ) )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('43',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('44',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ X16 )
       != ( sk_C_1 @ X13 @ X14 ) )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ X0 )
       != ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ sk_B_1 @ sk_B_1 @ X0 )
       != ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ sk_B_1 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_pre_topc @ sk_A ) )
        | ( ( k9_subset_1 @ sk_B_1 @ sk_B_1 @ X0 )
         != ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','54'])).

thf('56',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('57',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X6: $i] :
      ( ~ ( v1_tdlat_3 @ X6 )
      | ( ( u1_pre_topc @ X6 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('59',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k9_setfam_1 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k9_setfam_1 @ sk_B_1 ) )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k9_setfam_1 @ sk_B_1 ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ sk_B_1 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
        | ( ( k9_subset_1 @ sk_B_1 @ sk_B_1 @ X0 )
         != ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ sk_B_1 ) )
         != ( sk_C_1 @ sk_B_1 @ sk_A ) )
        | ~ ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ ( k9_setfam_1 @ sk_B_1 ) )
        | ~ ( v3_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_A )
        | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','63'])).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('68',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('70',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('83',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('86',plain,
    ( ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('89',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_tdlat_3 @ X25 )
      | ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('90',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('91',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_tdlat_3 @ X25 )
      | ( v3_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k9_setfam_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_tdlat_3 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( v3_pre_topc @ ( k9_subset_1 @ sk_B_1 @ X0 @ sk_B_1 ) @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( v3_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
         != ( sk_C_1 @ sk_B_1 @ sk_A ) )
        | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['64','79','80','99'])).

thf('101',plain,
    ( ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
       != ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','100'])).

thf('102',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_tdlat_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','104'])).

thf('106',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','105'])).

thf('107',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X6: $i] :
      ( ( ( u1_pre_topc @ X6 )
       != ( k9_setfam_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_tdlat_3 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('109',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k9_setfam_1 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k9_setfam_1 @ sk_B_1 ) )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('113',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X20 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('114',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('115',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('116',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X20 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['112','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('121',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('123',plain,
    ( ~ ( r1_tarski @ ( k9_setfam_1 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k9_setfam_1 @ sk_B_1 )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('124',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('125',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_setfam_1 @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k9_setfam_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_setfam_1 @ X0 ) @ X1 )
      | ( ( k3_xboole_0 @ ( sk_C @ X1 @ ( k9_setfam_1 @ X0 ) ) @ X0 )
        = ( sk_C @ X1 @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_setfam_1 @ X0 ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( sk_C @ X1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( sk_C @ X1 @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('136',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ ( sk_D @ X15 @ X13 @ X14 ) )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('137',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('138',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('139',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ ( sk_D @ X15 @ X13 @ X14 ) )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = X1 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( sk_D @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_D @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
        = ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['133','143'])).

thf('145',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('146',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('147',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','104','146'])).

thf('148',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['145','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_B_1 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['144','148','149','150','151','152','153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('157',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('159',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('160',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('161',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('162',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('163',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','164'])).

thf('166',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['145','147'])).

thf('168',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( k9_setfam_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['165','166','167','168','169','170','171'])).

thf('173',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( k9_setfam_1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ ( k9_setfam_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['156','174'])).

thf('176',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ sk_B_1 @ X1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      = ( k3_xboole_0 @ X1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['155','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ ( k9_setfam_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['156','174'])).

thf('180',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('181',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) )
      = ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_1 )
      = ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B_1 ) @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['178','185'])).

thf('187',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('189',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X17 @ X18 @ X19 ) @ ( k9_setfam_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('197',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['195','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['194','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['187','202'])).

thf('204',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('207',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( k9_setfam_1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('210',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_B_1 @ sk_A ) @ ( k9_setfam_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('212',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('213',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('214',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k9_setfam_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( sk_D @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_B_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['210','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('220',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('222',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v3_pre_topc @ ( sk_D @ X15 @ X13 @ X14 ) @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('223',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('224',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('225',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v3_pre_topc @ ( sk_D @ X15 @ X13 @ X14 ) @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k9_setfam_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v3_pre_topc @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['221','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['220','226'])).

thf('228',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['145','147'])).

thf('230',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ sk_B_1 ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['227','228','229','230','231','232'])).

thf('234',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( v3_pre_topc @ ( sk_D @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['219','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_B_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['218','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ X1 ) @ X0 ) @ sk_B_1 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['207','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['186','238'])).

thf('240',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('242',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['240','248'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('255',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('256',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) @ X0 )
      = ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) )
      = ( k9_subset_1 @ X0 @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('260',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['195','200'])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('262',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['195','200'])).

thf('263',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['258','259','260','261','262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['253','263'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X1 )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['264','265','271'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('274',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['239','272','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k9_setfam_1 @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ ( k9_setfam_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','274'])).

thf('276',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('277',plain,
    ( ( r1_tarski @ ( k9_setfam_1 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ ( k9_setfam_1 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    r1_tarski @ ( k9_setfam_1 @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['277'])).

thf('279',plain,
    ( ( k9_setfam_1 @ sk_B_1 )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['123','278'])).

thf('280',plain,
    ( ( ( k9_setfam_1 @ sk_B_1 )
     != ( k9_setfam_1 @ sk_B_1 ) )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['111','279'])).

thf('281',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(simplify,[status(thm)],['280'])).

thf('282',plain,(
    $false ),
    inference(demod,[status(thm)],['106','281'])).


%------------------------------------------------------------------------------
