%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tV94SNWDM1

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:36 EST 2020

% Result     : Theorem 23.68s
% Output     : Refutation 23.68s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 321 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          :  711 (2766 expanded)
%              Number of equality atoms :   38 ( 115 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( v4_pre_topc @ ( sk_B @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('2',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d6_tex_2,axiom,(
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
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( sk_C @ X29 @ X30 ) @ X29 )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('20',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('25',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X29: $i,X30: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v4_pre_topc @ X32 @ X30 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ X32 )
       != ( sk_C @ X29 @ X30 ) )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X8 @ X10 @ X9 )
        = ( k9_subset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','54'])).

thf('56',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('57',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['33','55','56','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tV94SNWDM1
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 23.68/23.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 23.68/23.87  % Solved by: fo/fo7.sh
% 23.68/23.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 23.68/23.87  % done 27044 iterations in 23.423s
% 23.68/23.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 23.68/23.87  % SZS output start Refutation
% 23.68/23.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 23.68/23.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 23.68/23.87  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 23.68/23.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 23.68/23.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 23.68/23.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 23.68/23.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 23.68/23.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 23.68/23.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 23.68/23.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 23.68/23.87  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 23.68/23.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 23.68/23.87  thf(sk_B_type, type, sk_B: $i > $i).
% 23.68/23.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 23.68/23.87  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 23.68/23.87  thf(sk_A_type, type, sk_A: $i).
% 23.68/23.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 23.68/23.87  thf(t35_tex_2, conjecture,
% 23.68/23.87    (![A:$i]:
% 23.68/23.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.68/23.87       ( ![B:$i]:
% 23.68/23.87         ( ( ( v1_xboole_0 @ B ) & 
% 23.68/23.87             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 23.68/23.87           ( v2_tex_2 @ B @ A ) ) ) ))).
% 23.68/23.87  thf(zf_stmt_0, negated_conjecture,
% 23.68/23.87    (~( ![A:$i]:
% 23.68/23.87        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 23.68/23.87            ( l1_pre_topc @ A ) ) =>
% 23.68/23.87          ( ![B:$i]:
% 23.68/23.87            ( ( ( v1_xboole_0 @ B ) & 
% 23.68/23.87                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 23.68/23.87              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 23.68/23.87    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 23.68/23.87  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf(rc7_pre_topc, axiom,
% 23.68/23.87    (![A:$i]:
% 23.68/23.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.68/23.87       ( ?[B:$i]:
% 23.68/23.87         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 23.68/23.87           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 23.68/23.87  thf('1', plain,
% 23.68/23.87      (![X28 : $i]:
% 23.68/23.87         ((v4_pre_topc @ (sk_B @ X28) @ X28)
% 23.68/23.87          | ~ (l1_pre_topc @ X28)
% 23.68/23.87          | ~ (v2_pre_topc @ X28)
% 23.68/23.87          | (v2_struct_0 @ X28))),
% 23.68/23.87      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 23.68/23.87  thf('2', plain,
% 23.68/23.87      (![X28 : $i]:
% 23.68/23.87         ((m1_subset_1 @ (sk_B @ X28) @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 23.68/23.87          | ~ (l1_pre_topc @ X28)
% 23.68/23.87          | ~ (v2_pre_topc @ X28)
% 23.68/23.87          | (v2_struct_0 @ X28))),
% 23.68/23.87      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 23.68/23.87  thf(l13_xboole_0, axiom,
% 23.68/23.87    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 23.68/23.87  thf('3', plain,
% 23.68/23.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 23.68/23.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 23.68/23.87  thf('4', plain,
% 23.68/23.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 23.68/23.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 23.68/23.87  thf(t4_subset_1, axiom,
% 23.68/23.87    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 23.68/23.87  thf('5', plain,
% 23.68/23.87      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 23.68/23.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 23.68/23.87  thf('6', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 23.68/23.87      inference('sup+', [status(thm)], ['4', '5'])).
% 23.68/23.87  thf(d6_tex_2, axiom,
% 23.68/23.87    (![A:$i]:
% 23.68/23.87     ( ( l1_pre_topc @ A ) =>
% 23.68/23.87       ( ![B:$i]:
% 23.68/23.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.68/23.87           ( ( v2_tex_2 @ B @ A ) <=>
% 23.68/23.87             ( ![C:$i]:
% 23.68/23.87               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.68/23.87                 ( ~( ( r1_tarski @ C @ B ) & 
% 23.68/23.87                      ( ![D:$i]:
% 23.68/23.87                        ( ( m1_subset_1 @
% 23.68/23.87                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.68/23.87                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 23.68/23.87                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 23.68/23.87                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 23.68/23.87  thf('7', plain,
% 23.68/23.87      (![X29 : $i, X30 : $i]:
% 23.68/23.87         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 23.68/23.87          | (r1_tarski @ (sk_C @ X29 @ X30) @ X29)
% 23.68/23.87          | (v2_tex_2 @ X29 @ X30)
% 23.68/23.87          | ~ (l1_pre_topc @ X30))),
% 23.68/23.87      inference('cnf', [status(esa)], [d6_tex_2])).
% 23.68/23.87  thf('8', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         (~ (v1_xboole_0 @ X1)
% 23.68/23.87          | ~ (l1_pre_topc @ X0)
% 23.68/23.87          | (v2_tex_2 @ X1 @ X0)
% 23.68/23.87          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 23.68/23.87      inference('sup-', [status(thm)], ['6', '7'])).
% 23.68/23.87  thf(t3_xboole_1, axiom,
% 23.68/23.87    (![A:$i]:
% 23.68/23.87     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 23.68/23.87  thf('9', plain,
% 23.68/23.87      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 23.68/23.87      inference('cnf', [status(esa)], [t3_xboole_1])).
% 23.68/23.87  thf('10', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 23.68/23.87          | ~ (l1_pre_topc @ X0)
% 23.68/23.87          | ~ (v1_xboole_0 @ k1_xboole_0)
% 23.68/23.87          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 23.68/23.87      inference('sup-', [status(thm)], ['8', '9'])).
% 23.68/23.87  thf('11', plain, ((v1_xboole_0 @ sk_B_1)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('12', plain, ((v1_xboole_0 @ sk_B_1)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('13', plain,
% 23.68/23.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 23.68/23.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 23.68/23.87  thf('14', plain, (((sk_B_1) = (k1_xboole_0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['12', '13'])).
% 23.68/23.87  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 23.68/23.87      inference('demod', [status(thm)], ['11', '14'])).
% 23.68/23.87  thf('16', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 23.68/23.87          | ~ (l1_pre_topc @ X0)
% 23.68/23.87          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 23.68/23.87      inference('demod', [status(thm)], ['10', '15'])).
% 23.68/23.87  thf('17', plain,
% 23.68/23.87      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 23.68/23.87      inference('cnf', [status(esa)], [l13_xboole_0])).
% 23.68/23.87  thf('18', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('19', plain, (((sk_B_1) = (k1_xboole_0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['12', '13'])).
% 23.68/23.87  thf('20', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 23.68/23.87      inference('demod', [status(thm)], ['18', '19'])).
% 23.68/23.87  thf('21', plain,
% 23.68/23.87      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['17', '20'])).
% 23.68/23.87  thf('22', plain,
% 23.68/23.87      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 23.68/23.87        | ~ (l1_pre_topc @ sk_A)
% 23.68/23.87        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['16', '21'])).
% 23.68/23.87  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 23.68/23.87      inference('demod', [status(thm)], ['11', '14'])).
% 23.68/23.87  thf('25', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 23.68/23.87      inference('demod', [status(thm)], ['22', '23', '24'])).
% 23.68/23.87  thf('26', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 23.68/23.87      inference('sup+', [status(thm)], ['3', '25'])).
% 23.68/23.87  thf('27', plain,
% 23.68/23.87      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 23.68/23.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 23.68/23.87  thf('28', plain,
% 23.68/23.87      (![X29 : $i, X30 : $i]:
% 23.68/23.87         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 23.68/23.87          | (m1_subset_1 @ (sk_C @ X29 @ X30) @ 
% 23.68/23.87             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 23.68/23.87          | (v2_tex_2 @ X29 @ X30)
% 23.68/23.87          | ~ (l1_pre_topc @ X30))),
% 23.68/23.87      inference('cnf', [status(esa)], [d6_tex_2])).
% 23.68/23.87  thf('29', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         (~ (l1_pre_topc @ X0)
% 23.68/23.87          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 23.68/23.87          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 23.68/23.87             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 23.68/23.87      inference('sup-', [status(thm)], ['27', '28'])).
% 23.68/23.87  thf('30', plain,
% 23.68/23.87      (![X29 : $i, X30 : $i, X32 : $i]:
% 23.68/23.87         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 23.68/23.87          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 23.68/23.87          | ~ (v4_pre_topc @ X32 @ X30)
% 23.68/23.87          | ((k9_subset_1 @ (u1_struct_0 @ X30) @ X29 @ X32)
% 23.68/23.87              != (sk_C @ X29 @ X30))
% 23.68/23.87          | (v2_tex_2 @ X29 @ X30)
% 23.68/23.87          | ~ (l1_pre_topc @ X30))),
% 23.68/23.87      inference('cnf', [status(esa)], [d6_tex_2])).
% 23.68/23.87  thf('31', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 23.68/23.87          | ~ (l1_pre_topc @ X0)
% 23.68/23.87          | ~ (l1_pre_topc @ X0)
% 23.68/23.87          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 23.68/23.87          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 23.68/23.87              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 23.68/23.87          | ~ (v4_pre_topc @ X1 @ X0)
% 23.68/23.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 23.68/23.87      inference('sup-', [status(thm)], ['29', '30'])).
% 23.68/23.87  thf('32', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 23.68/23.87          | ~ (v4_pre_topc @ X1 @ X0)
% 23.68/23.87          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 23.68/23.87              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 23.68/23.87          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 23.68/23.87          | ~ (l1_pre_topc @ X0)
% 23.68/23.87          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 23.68/23.87      inference('simplify', [status(thm)], ['31'])).
% 23.68/23.87  thf('33', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ X0)
% 23.68/23.87            != (sk_C @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))
% 23.68/23.87          | ~ (v1_xboole_0 @ k1_xboole_0)
% 23.68/23.87          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 23.68/23.87          | ~ (l1_pre_topc @ sk_A)
% 23.68/23.87          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 23.68/23.87          | ~ (v4_pre_topc @ X0 @ sk_A)
% 23.68/23.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 23.68/23.87      inference('sup-', [status(thm)], ['26', '32'])).
% 23.68/23.87  thf('34', plain,
% 23.68/23.87      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 23.68/23.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 23.68/23.87  thf(commutativity_k9_subset_1, axiom,
% 23.68/23.87    (![A:$i,B:$i,C:$i]:
% 23.68/23.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 23.68/23.87       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 23.68/23.87  thf('35', plain,
% 23.68/23.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 23.68/23.87         (((k9_subset_1 @ X8 @ X10 @ X9) = (k9_subset_1 @ X8 @ X9 @ X10))
% 23.68/23.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 23.68/23.87      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 23.68/23.87  thf('36', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 23.68/23.87           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 23.68/23.87      inference('sup-', [status(thm)], ['34', '35'])).
% 23.68/23.87  thf('37', plain,
% 23.68/23.87      (![X21 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 23.68/23.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 23.68/23.87  thf(redefinition_k9_subset_1, axiom,
% 23.68/23.87    (![A:$i,B:$i,C:$i]:
% 23.68/23.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 23.68/23.87       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 23.68/23.87  thf('38', plain,
% 23.68/23.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 23.68/23.87         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 23.68/23.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 23.68/23.87      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 23.68/23.87  thf('39', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 23.68/23.87           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['37', '38'])).
% 23.68/23.87  thf(d10_xboole_0, axiom,
% 23.68/23.87    (![A:$i,B:$i]:
% 23.68/23.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 23.68/23.87  thf('40', plain,
% 23.68/23.87      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 23.68/23.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.68/23.87  thf('41', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 23.68/23.87      inference('simplify', [status(thm)], ['40'])).
% 23.68/23.87  thf(t3_subset, axiom,
% 23.68/23.87    (![A:$i,B:$i]:
% 23.68/23.87     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 23.68/23.87  thf('42', plain,
% 23.68/23.87      (![X22 : $i, X24 : $i]:
% 23.68/23.87         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 23.68/23.87      inference('cnf', [status(esa)], [t3_subset])).
% 23.68/23.87  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['41', '42'])).
% 23.68/23.87  thf(dt_k9_subset_1, axiom,
% 23.68/23.87    (![A:$i,B:$i,C:$i]:
% 23.68/23.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 23.68/23.87       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 23.68/23.87  thf('44', plain,
% 23.68/23.87      (![X12 : $i, X13 : $i, X14 : $i]:
% 23.68/23.87         ((m1_subset_1 @ (k9_subset_1 @ X12 @ X13 @ X14) @ (k1_zfmisc_1 @ X12))
% 23.68/23.87          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X12)))),
% 23.68/23.87      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 23.68/23.87  thf('45', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['43', '44'])).
% 23.68/23.87  thf('46', plain,
% 23.68/23.87      (![X22 : $i, X23 : $i]:
% 23.68/23.87         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 23.68/23.87      inference('cnf', [status(esa)], [t3_subset])).
% 23.68/23.87  thf('47', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 23.68/23.87      inference('sup-', [status(thm)], ['45', '46'])).
% 23.68/23.87  thf('48', plain,
% 23.68/23.87      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 23.68/23.87      inference('cnf', [status(esa)], [t3_xboole_1])).
% 23.68/23.87  thf('49', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         ((k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['47', '48'])).
% 23.68/23.87  thf('50', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['41', '42'])).
% 23.68/23.87  thf('51', plain,
% 23.68/23.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 23.68/23.87         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 23.68/23.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 23.68/23.87      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 23.68/23.87  thf('52', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 23.68/23.87      inference('sup-', [status(thm)], ['50', '51'])).
% 23.68/23.87  thf('53', plain,
% 23.68/23.87      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 23.68/23.87      inference('demod', [status(thm)], ['49', '52'])).
% 23.68/23.87  thf('54', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 23.68/23.87      inference('demod', [status(thm)], ['39', '53'])).
% 23.68/23.87  thf('55', plain,
% 23.68/23.87      (![X0 : $i, X1 : $i]:
% 23.68/23.87         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 23.68/23.87      inference('demod', [status(thm)], ['36', '54'])).
% 23.68/23.87  thf('56', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 23.68/23.87      inference('demod', [status(thm)], ['22', '23', '24'])).
% 23.68/23.87  thf('57', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 23.68/23.87      inference('demod', [status(thm)], ['22', '23', '24'])).
% 23.68/23.87  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 23.68/23.87      inference('demod', [status(thm)], ['11', '14'])).
% 23.68/23.87  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('60', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 23.68/23.87      inference('demod', [status(thm)], ['22', '23', '24'])).
% 23.68/23.87  thf('61', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         (((k1_xboole_0) != (k1_xboole_0))
% 23.68/23.87          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 23.68/23.87          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 23.68/23.87          | ~ (v4_pre_topc @ X0 @ sk_A)
% 23.68/23.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 23.68/23.87      inference('demod', [status(thm)],
% 23.68/23.87                ['33', '55', '56', '57', '58', '59', '60'])).
% 23.68/23.87  thf('62', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 23.68/23.87          | ~ (v4_pre_topc @ X0 @ sk_A)
% 23.68/23.87          | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 23.68/23.87      inference('simplify', [status(thm)], ['61'])).
% 23.68/23.87  thf('63', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 23.68/23.87      inference('demod', [status(thm)], ['18', '19'])).
% 23.68/23.87  thf('64', plain,
% 23.68/23.87      (![X0 : $i]:
% 23.68/23.87         (~ (v4_pre_topc @ X0 @ sk_A)
% 23.68/23.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 23.68/23.87      inference('clc', [status(thm)], ['62', '63'])).
% 23.68/23.87  thf('65', plain,
% 23.68/23.87      (((v2_struct_0 @ sk_A)
% 23.68/23.87        | ~ (v2_pre_topc @ sk_A)
% 23.68/23.87        | ~ (l1_pre_topc @ sk_A)
% 23.68/23.87        | ~ (v4_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 23.68/23.87      inference('sup-', [status(thm)], ['2', '64'])).
% 23.68/23.87  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('68', plain,
% 23.68/23.87      (((v2_struct_0 @ sk_A) | ~ (v4_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 23.68/23.87      inference('demod', [status(thm)], ['65', '66', '67'])).
% 23.68/23.87  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('70', plain, (~ (v4_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 23.68/23.87      inference('clc', [status(thm)], ['68', '69'])).
% 23.68/23.87  thf('71', plain,
% 23.68/23.87      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 23.68/23.87      inference('sup-', [status(thm)], ['1', '70'])).
% 23.68/23.87  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 23.68/23.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.68/23.87  thf('74', plain, ((v2_struct_0 @ sk_A)),
% 23.68/23.87      inference('demod', [status(thm)], ['71', '72', '73'])).
% 23.68/23.87  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 23.68/23.87  
% 23.68/23.87  % SZS output end Refutation
% 23.68/23.87  
% 23.68/23.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
