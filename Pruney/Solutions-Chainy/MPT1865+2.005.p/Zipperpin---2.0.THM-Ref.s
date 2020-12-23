%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tPKmrRTHbY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:21 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 238 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  910 (3397 expanded)
%              Number of equality atoms :   33 ( 124 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t33_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( v4_pre_topc @ D @ A )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( sk_D_1 @ X27 @ X25 @ X26 ) )
        = ( k1_tarski @ X27 ) )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t32_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k3_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ( m1_subset_1 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','42'])).

thf('44',plain,(
    ! [X28: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X28 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X28 @ sk_A )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('46',plain,(
    ! [X28: $i] :
      ( ( ( k3_xboole_0 @ X28 @ sk_B )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X28 @ sk_A )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
      | ( ( k3_xboole_0 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ sk_B )
       != ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ( v4_pre_topc @ ( sk_D @ X23 @ X21 @ X22 ) @ X22 )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('57',plain,(
    ! [X0: $i] :
      ( v4_pre_topc @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ ( sk_D @ X23 @ X21 @ X22 ) )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k3_xboole_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ sk_B )
        = ( k3_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B @ sk_A ) @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['47','57','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tPKmrRTHbY
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:27:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.91/2.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.91/2.09  % Solved by: fo/fo7.sh
% 1.91/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.09  % done 1873 iterations in 1.632s
% 1.91/2.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.91/2.09  % SZS output start Refutation
% 1.91/2.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.91/2.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.91/2.09  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.91/2.09  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.91/2.09  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.91/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.09  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.91/2.09  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.91/2.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.91/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.09  thf(sk_B_type, type, sk_B: $i).
% 1.91/2.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.91/2.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.91/2.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.91/2.09  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.91/2.09  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.91/2.09  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.91/2.09  thf(t33_tex_2, conjecture,
% 1.91/2.09    (![A:$i]:
% 1.91/2.09     ( ( l1_pre_topc @ A ) =>
% 1.91/2.09       ( ![B:$i]:
% 1.91/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09           ( ( v2_tex_2 @ B @ A ) =>
% 1.91/2.09             ( ![C:$i]:
% 1.91/2.09               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.91/2.09                 ( ~( ( r2_hidden @ C @ B ) & 
% 1.91/2.09                      ( ![D:$i]:
% 1.91/2.09                        ( ( m1_subset_1 @
% 1.91/2.09                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.91/2.09                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.91/2.09                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.09    (~( ![A:$i]:
% 1.91/2.09        ( ( l1_pre_topc @ A ) =>
% 1.91/2.09          ( ![B:$i]:
% 1.91/2.09            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09              ( ( v2_tex_2 @ B @ A ) =>
% 1.91/2.09                ( ![C:$i]:
% 1.91/2.09                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.91/2.09                    ( ~( ( r2_hidden @ C @ B ) & 
% 1.91/2.09                         ( ![D:$i]:
% 1.91/2.09                           ( ( m1_subset_1 @
% 1.91/2.09                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.91/2.09                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.91/2.09                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.91/2.09    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 1.91/2.09  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('1', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(t32_tex_2, axiom,
% 1.91/2.09    (![A:$i]:
% 1.91/2.09     ( ( l1_pre_topc @ A ) =>
% 1.91/2.09       ( ![B:$i]:
% 1.91/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09           ( ( v2_tex_2 @ B @ A ) =>
% 1.91/2.09             ( ![C:$i]:
% 1.91/2.09               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.91/2.09                 ( ~( ( r2_hidden @ C @ B ) & 
% 1.91/2.09                      ( ![D:$i]:
% 1.91/2.09                        ( ( m1_subset_1 @
% 1.91/2.09                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 1.91/2.09                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.91/2.09                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.09  thf('2', plain,
% 1.91/2.09      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.91/2.09          | ((k9_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 1.91/2.09              (sk_D_1 @ X27 @ X25 @ X26)) = (k1_tarski @ X27))
% 1.91/2.09          | ~ (r2_hidden @ X27 @ X25)
% 1.91/2.09          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 1.91/2.09          | ~ (v2_tex_2 @ X25 @ X26)
% 1.91/2.09          | ~ (l1_pre_topc @ X26))),
% 1.91/2.09      inference('cnf', [status(esa)], [t32_tex_2])).
% 1.91/2.09  thf('3', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (l1_pre_topc @ sk_A)
% 1.91/2.09          | ~ (v2_tex_2 @ sk_B @ sk_A)
% 1.91/2.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.91/2.09          | ~ (r2_hidden @ X0 @ sk_B)
% 1.91/2.09          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.91/2.09              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (k1_tarski @ X0)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['1', '2'])).
% 1.91/2.09  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('5', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('6', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(commutativity_k9_subset_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.09       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 1.91/2.09  thf('7', plain,
% 1.91/2.09      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.91/2.09         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 1.91/2.09          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.91/2.09      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.91/2.09  thf('8', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.91/2.09           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['6', '7'])).
% 1.91/2.09  thf('9', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(redefinition_k9_subset_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.09       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.91/2.09  thf('10', plain,
% 1.91/2.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.91/2.09         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 1.91/2.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.91/2.09      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.91/2.09  thf('11', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.91/2.09           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['9', '10'])).
% 1.91/2.09  thf('12', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((k3_xboole_0 @ X0 @ sk_B)
% 1.91/2.09           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.91/2.09      inference('demod', [status(thm)], ['8', '11'])).
% 1.91/2.09  thf('13', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.91/2.09          | ~ (r2_hidden @ X0 @ sk_B)
% 1.91/2.09          | ((k3_xboole_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 1.91/2.09              = (k1_tarski @ X0)))),
% 1.91/2.09      inference('demod', [status(thm)], ['3', '4', '5', '12'])).
% 1.91/2.09  thf('14', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(t4_subset, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.91/2.09       ( m1_subset_1 @ A @ C ) ))).
% 1.91/2.09  thf('15', plain,
% 1.91/2.09      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X18 @ X19)
% 1.91/2.09          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.91/2.09          | (m1_subset_1 @ X18 @ X20))),
% 1.91/2.09      inference('cnf', [status(esa)], [t4_subset])).
% 1.91/2.09  thf('16', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['14', '15'])).
% 1.91/2.09  thf('17', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (((k3_xboole_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_B)
% 1.91/2.09            = (k1_tarski @ X0))
% 1.91/2.09          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.91/2.09      inference('clc', [status(thm)], ['13', '16'])).
% 1.91/2.09  thf('18', plain,
% 1.91/2.09      (((k3_xboole_0 @ (sk_D_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 1.91/2.09         = (k1_tarski @ sk_C_1))),
% 1.91/2.09      inference('sup-', [status(thm)], ['0', '17'])).
% 1.91/2.09  thf('19', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(dt_k9_subset_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.09       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.91/2.09  thf('20', plain,
% 1.91/2.09      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.91/2.09         ((m1_subset_1 @ (k9_subset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 1.91/2.09          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X9)))),
% 1.91/2.09      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.91/2.09  thf('21', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 1.91/2.09          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['19', '20'])).
% 1.91/2.09  thf('22', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.91/2.09           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['9', '10'])).
% 1.91/2.09  thf('23', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.91/2.09          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.91/2.09  thf('24', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(d6_tex_2, axiom,
% 1.91/2.09    (![A:$i]:
% 1.91/2.09     ( ( l1_pre_topc @ A ) =>
% 1.91/2.09       ( ![B:$i]:
% 1.91/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09           ( ( v2_tex_2 @ B @ A ) <=>
% 1.91/2.09             ( ![C:$i]:
% 1.91/2.09               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.91/2.09                      ( ![D:$i]:
% 1.91/2.09                        ( ( m1_subset_1 @
% 1.91/2.09                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.91/2.09                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.91/2.09                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.91/2.09                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.09  thf('25', plain,
% 1.91/2.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.91/2.09          | ~ (v2_tex_2 @ X21 @ X22)
% 1.91/2.09          | (m1_subset_1 @ (sk_D @ X23 @ X21 @ X22) @ 
% 1.91/2.09             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.91/2.09          | ~ (r1_tarski @ X23 @ X21)
% 1.91/2.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.91/2.09          | ~ (l1_pre_topc @ X22))),
% 1.91/2.09      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.91/2.09  thf('26', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (l1_pre_topc @ sk_A)
% 1.91/2.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ sk_B)
% 1.91/2.09          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 1.91/2.09             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.91/2.09      inference('sup-', [status(thm)], ['24', '25'])).
% 1.91/2.09  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('28', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('29', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ sk_B)
% 1.91/2.09          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 1.91/2.09             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.91/2.09      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.91/2.09  thf('30', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((m1_subset_1 @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ 
% 1.91/2.09           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['23', '29'])).
% 1.91/2.09  thf(d10_xboole_0, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.09  thf('31', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.91/2.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.91/2.09  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.91/2.09      inference('simplify', [status(thm)], ['31'])).
% 1.91/2.09  thf(t3_subset, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.91/2.09  thf('33', plain,
% 1.91/2.09      (![X15 : $i, X17 : $i]:
% 1.91/2.09         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.91/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.91/2.09  thf('34', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['32', '33'])).
% 1.91/2.09  thf('35', plain,
% 1.91/2.09      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.91/2.09         ((m1_subset_1 @ (k9_subset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 1.91/2.09          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X9)))),
% 1.91/2.09      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.91/2.09  thf('36', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['34', '35'])).
% 1.91/2.09  thf('37', plain,
% 1.91/2.09      (![X15 : $i, X16 : $i]:
% 1.91/2.09         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.91/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.91/2.09  thf('38', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 1.91/2.09      inference('sup-', [status(thm)], ['36', '37'])).
% 1.91/2.09  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['32', '33'])).
% 1.91/2.09  thf('40', plain,
% 1.91/2.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.91/2.09         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 1.91/2.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.91/2.09      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.91/2.09  thf('41', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['39', '40'])).
% 1.91/2.09  thf('42', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.91/2.09      inference('demod', [status(thm)], ['38', '41'])).
% 1.91/2.09  thf('43', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (m1_subset_1 @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ 
% 1.91/2.09          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('demod', [status(thm)], ['30', '42'])).
% 1.91/2.09  thf('44', plain,
% 1.91/2.09      (![X28 : $i]:
% 1.91/2.09         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X28)
% 1.91/2.09            != (k1_tarski @ sk_C_1))
% 1.91/2.09          | ~ (v4_pre_topc @ X28 @ sk_A)
% 1.91/2.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('45', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((k3_xboole_0 @ X0 @ sk_B)
% 1.91/2.09           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.91/2.09      inference('demod', [status(thm)], ['8', '11'])).
% 1.91/2.09  thf('46', plain,
% 1.91/2.09      (![X28 : $i]:
% 1.91/2.09         (((k3_xboole_0 @ X28 @ sk_B) != (k1_tarski @ sk_C_1))
% 1.91/2.09          | ~ (v4_pre_topc @ X28 @ sk_A)
% 1.91/2.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.91/2.09      inference('demod', [status(thm)], ['44', '45'])).
% 1.91/2.09  thf('47', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (v4_pre_topc @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ 
% 1.91/2.09             sk_A)
% 1.91/2.09          | ((k3_xboole_0 @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ 
% 1.91/2.09              sk_B) != (k1_tarski @ sk_C_1)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['43', '46'])).
% 1.91/2.09  thf('48', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.91/2.09          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.91/2.09  thf('49', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('50', plain,
% 1.91/2.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.91/2.09          | ~ (v2_tex_2 @ X21 @ X22)
% 1.91/2.09          | (v4_pre_topc @ (sk_D @ X23 @ X21 @ X22) @ X22)
% 1.91/2.09          | ~ (r1_tarski @ X23 @ X21)
% 1.91/2.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.91/2.09          | ~ (l1_pre_topc @ X22))),
% 1.91/2.09      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.91/2.09  thf('51', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (l1_pre_topc @ sk_A)
% 1.91/2.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ sk_B)
% 1.91/2.09          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 1.91/2.09          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.91/2.09      inference('sup-', [status(thm)], ['49', '50'])).
% 1.91/2.09  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('53', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('54', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ sk_B)
% 1.91/2.09          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 1.91/2.09      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.91/2.09  thf('55', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((v4_pre_topc @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ 
% 1.91/2.09           sk_A)
% 1.91/2.09          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['48', '54'])).
% 1.91/2.09  thf('56', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.91/2.09      inference('demod', [status(thm)], ['38', '41'])).
% 1.91/2.09  thf('57', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (v4_pre_topc @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ sk_A)),
% 1.91/2.09      inference('demod', [status(thm)], ['55', '56'])).
% 1.91/2.09  thf('58', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.91/2.09          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.91/2.09  thf('59', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('60', plain,
% 1.91/2.09      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.91/2.09          | ~ (v2_tex_2 @ X21 @ X22)
% 1.91/2.09          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ 
% 1.91/2.09              (sk_D @ X23 @ X21 @ X22)) = (X23))
% 1.91/2.09          | ~ (r1_tarski @ X23 @ X21)
% 1.91/2.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.91/2.09          | ~ (l1_pre_topc @ X22))),
% 1.91/2.09      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.91/2.09  thf('61', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (l1_pre_topc @ sk_A)
% 1.91/2.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ sk_B)
% 1.91/2.09          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.91/2.09              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 1.91/2.09          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.91/2.09      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.09  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('63', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('64', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ sk_B)
% 1.91/2.09          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.91/2.09              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 1.91/2.09      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.91/2.09  thf('65', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((k3_xboole_0 @ X0 @ sk_B)
% 1.91/2.09           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.91/2.09      inference('demod', [status(thm)], ['8', '11'])).
% 1.91/2.09  thf('66', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ sk_B)
% 1.91/2.09          | ((k3_xboole_0 @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B) = (X0)))),
% 1.91/2.09      inference('demod', [status(thm)], ['64', '65'])).
% 1.91/2.09  thf('67', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (((k3_xboole_0 @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ 
% 1.91/2.09            sk_B) = (k3_xboole_0 @ X0 @ sk_B))
% 1.91/2.09          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['58', '66'])).
% 1.91/2.09  thf('68', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.91/2.09      inference('demod', [status(thm)], ['38', '41'])).
% 1.91/2.09  thf('69', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((k3_xboole_0 @ (sk_D @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B @ sk_A) @ 
% 1.91/2.09           sk_B) = (k3_xboole_0 @ X0 @ sk_B))),
% 1.91/2.09      inference('demod', [status(thm)], ['67', '68'])).
% 1.91/2.09  thf('70', plain,
% 1.91/2.09      (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) != (k1_tarski @ sk_C_1))),
% 1.91/2.09      inference('demod', [status(thm)], ['47', '57', '69'])).
% 1.91/2.09  thf('71', plain, ($false),
% 1.91/2.09      inference('simplify_reflect-', [status(thm)], ['18', '70'])).
% 1.91/2.09  
% 1.91/2.09  % SZS output end Refutation
% 1.91/2.09  
% 1.91/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
