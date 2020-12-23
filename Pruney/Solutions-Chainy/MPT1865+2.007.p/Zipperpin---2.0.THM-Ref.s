%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hSEGwXCTDu

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:21 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 221 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  784 (2995 expanded)
%              Number of equality atoms :   16 (  79 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('1',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X14 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_B_1 ) @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_B @ sk_B_1 ) @ sk_C_2 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_tarski @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('18',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X14 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C_2 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( m1_subset_1 @ ( sk_D @ X29 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('39',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_2 @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X31: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X31 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v4_pre_topc @ X31 @ sk_A )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( v4_pre_topc @ ( sk_D @ X29 @ X27 @ X28 ) @ X28 )
      | ~ ( r1_tarski @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( sk_D @ X29 @ X27 @ X28 ) )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','66'])).

thf('68',plain,(
    $false ),
    inference('sup-',[status(thm)],['10','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hSEGwXCTDu
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.66/1.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.66/1.86  % Solved by: fo/fo7.sh
% 1.66/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.86  % done 727 iterations in 1.400s
% 1.66/1.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.66/1.86  % SZS output start Refutation
% 1.66/1.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.66/1.86  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.66/1.86  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.66/1.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.66/1.86  thf(sk_B_type, type, sk_B: $i > $i).
% 1.66/1.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.66/1.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.66/1.86  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.66/1.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.66/1.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.66/1.86  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.66/1.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.86  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.66/1.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.66/1.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.66/1.86  thf(d1_xboole_0, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.66/1.86  thf('0', plain,
% 1.66/1.86      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.66/1.86      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.66/1.86  thf(t33_tex_2, conjecture,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( l1_pre_topc @ A ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.86           ( ( v2_tex_2 @ B @ A ) =>
% 1.66/1.86             ( ![C:$i]:
% 1.66/1.86               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.66/1.86                 ( ~( ( r2_hidden @ C @ B ) & 
% 1.66/1.86                      ( ![D:$i]:
% 1.66/1.86                        ( ( m1_subset_1 @
% 1.66/1.86                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.86                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.66/1.86                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.66/1.86                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.66/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.86    (~( ![A:$i]:
% 1.66/1.86        ( ( l1_pre_topc @ A ) =>
% 1.66/1.86          ( ![B:$i]:
% 1.66/1.86            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.86              ( ( v2_tex_2 @ B @ A ) =>
% 1.66/1.86                ( ![C:$i]:
% 1.66/1.86                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.66/1.86                    ( ~( ( r2_hidden @ C @ B ) & 
% 1.66/1.86                         ( ![D:$i]:
% 1.66/1.86                           ( ( m1_subset_1 @
% 1.66/1.86                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.86                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.66/1.86                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.66/1.86                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.66/1.86    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 1.66/1.86  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(t38_zfmisc_1, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.66/1.86       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.66/1.86  thf('2', plain,
% 1.66/1.86      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.66/1.86         ((r1_tarski @ (k2_tarski @ X14 @ X16) @ X17)
% 1.66/1.86          | ~ (r2_hidden @ X16 @ X17)
% 1.66/1.86          | ~ (r2_hidden @ X14 @ X17))),
% 1.66/1.86      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.66/1.86  thf('3', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.66/1.86          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ sk_B_1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['1', '2'])).
% 1.66/1.86  thf('4', plain,
% 1.66/1.86      (((v1_xboole_0 @ sk_B_1)
% 1.66/1.86        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_B_1) @ sk_C_2) @ sk_B_1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['0', '3'])).
% 1.66/1.86  thf('5', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('6', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.66/1.86  thf('7', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.66/1.86      inference('sup-', [status(thm)], ['5', '6'])).
% 1.66/1.86  thf('8', plain,
% 1.66/1.86      ((r1_tarski @ (k2_tarski @ (sk_B @ sk_B_1) @ sk_C_2) @ sk_B_1)),
% 1.66/1.86      inference('clc', [status(thm)], ['4', '7'])).
% 1.66/1.86  thf('9', plain,
% 1.66/1.86      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.66/1.86         ((r2_hidden @ X14 @ X15)
% 1.66/1.86          | ~ (r1_tarski @ (k2_tarski @ X14 @ X16) @ X15))),
% 1.66/1.86      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.66/1.86  thf('10', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 1.66/1.86      inference('sup-', [status(thm)], ['8', '9'])).
% 1.66/1.86  thf('11', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(t5_subset, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.66/1.86          ( v1_xboole_0 @ C ) ) ))).
% 1.66/1.86  thf('12', plain,
% 1.66/1.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X22 @ X23)
% 1.66/1.86          | ~ (v1_xboole_0 @ X24)
% 1.66/1.86          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t5_subset])).
% 1.66/1.86  thf('13', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['11', '12'])).
% 1.66/1.86  thf('14', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(t2_subset, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( m1_subset_1 @ A @ B ) =>
% 1.66/1.86       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.66/1.86  thf('15', plain,
% 1.66/1.86      (![X20 : $i, X21 : $i]:
% 1.66/1.86         ((r2_hidden @ X20 @ X21)
% 1.66/1.86          | (v1_xboole_0 @ X21)
% 1.66/1.86          | ~ (m1_subset_1 @ X20 @ X21))),
% 1.66/1.86      inference('cnf', [status(esa)], [t2_subset])).
% 1.66/1.86  thf('16', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['14', '15'])).
% 1.66/1.86  thf('17', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['14', '15'])).
% 1.66/1.86  thf('18', plain,
% 1.66/1.86      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.66/1.86         ((r1_tarski @ (k2_tarski @ X14 @ X16) @ X17)
% 1.66/1.86          | ~ (r2_hidden @ X16 @ X17)
% 1.66/1.86          | ~ (r2_hidden @ X14 @ X17))),
% 1.66/1.86      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.66/1.86  thf('19', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['17', '18'])).
% 1.66/1.86  thf('20', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.66/1.86  thf('21', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 1.66/1.86          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('clc', [status(thm)], ['19', '20'])).
% 1.66/1.86  thf('22', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (r1_tarski @ (k2_tarski @ sk_C_2 @ sk_C_2) @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['16', '21'])).
% 1.66/1.86  thf(t69_enumset1, axiom,
% 1.66/1.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.66/1.86  thf('23', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.66/1.86  thf('24', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('demod', [status(thm)], ['22', '23'])).
% 1.66/1.86  thf(d1_zfmisc_1, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.66/1.86       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.66/1.86  thf('25', plain,
% 1.66/1.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.66/1.86         (~ (r1_tarski @ X9 @ X10)
% 1.66/1.86          | (r2_hidden @ X9 @ X11)
% 1.66/1.86          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 1.66/1.86      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.66/1.86  thf('26', plain,
% 1.66/1.86      (![X9 : $i, X10 : $i]:
% 1.66/1.86         ((r2_hidden @ X9 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X9 @ X10))),
% 1.66/1.86      inference('simplify', [status(thm)], ['25'])).
% 1.66/1.86  thf('27', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (r2_hidden @ (k1_tarski @ sk_C_2) @ 
% 1.66/1.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['24', '26'])).
% 1.66/1.86  thf(t1_subset, axiom,
% 1.66/1.86    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.66/1.86  thf('28', plain,
% 1.66/1.86      (![X18 : $i, X19 : $i]:
% 1.66/1.86         ((m1_subset_1 @ X18 @ X19) | ~ (r2_hidden @ X18 @ X19))),
% 1.66/1.86      inference('cnf', [status(esa)], [t1_subset])).
% 1.66/1.86  thf('29', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 1.66/1.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['27', '28'])).
% 1.66/1.86  thf('30', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(d6_tex_2, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( l1_pre_topc @ A ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.86           ( ( v2_tex_2 @ B @ A ) <=>
% 1.66/1.86             ( ![C:$i]:
% 1.66/1.86               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.86                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.66/1.86                      ( ![D:$i]:
% 1.66/1.86                        ( ( m1_subset_1 @
% 1.66/1.86                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.66/1.86                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.66/1.86                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.66/1.86                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.66/1.86  thf('31', plain,
% 1.66/1.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.66/1.86          | ~ (v2_tex_2 @ X27 @ X28)
% 1.66/1.86          | (m1_subset_1 @ (sk_D @ X29 @ X27 @ X28) @ 
% 1.66/1.86             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.66/1.86          | ~ (r1_tarski @ X29 @ X27)
% 1.66/1.86          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.66/1.86          | ~ (l1_pre_topc @ X28))),
% 1.66/1.86      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.66/1.86  thf('32', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (l1_pre_topc @ sk_A)
% 1.66/1.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.66/1.86          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ 
% 1.66/1.86             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['30', '31'])).
% 1.66/1.86  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('34', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('35', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.66/1.86          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ 
% 1.66/1.86             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.66/1.86      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.66/1.86  thf('36', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A) @ 
% 1.66/1.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['29', '35'])).
% 1.66/1.86  thf('37', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('38', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.66/1.86          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ sk_B_1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['1', '2'])).
% 1.66/1.86  thf('39', plain, ((r1_tarski @ (k2_tarski @ sk_C_2 @ sk_C_2) @ sk_B_1)),
% 1.66/1.86      inference('sup-', [status(thm)], ['37', '38'])).
% 1.66/1.86  thf('40', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.66/1.86  thf('41', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 1.66/1.86      inference('demod', [status(thm)], ['39', '40'])).
% 1.66/1.86  thf('42', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A) @ 
% 1.66/1.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.66/1.86      inference('demod', [status(thm)], ['36', '41'])).
% 1.66/1.86  thf('43', plain,
% 1.66/1.86      (![X31 : $i]:
% 1.66/1.86         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X31)
% 1.66/1.86            != (k1_tarski @ sk_C_2))
% 1.66/1.86          | ~ (v4_pre_topc @ X31 @ sk_A)
% 1.66/1.86          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('44', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | ~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A) @ sk_A)
% 1.66/1.86        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 1.66/1.86            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A))
% 1.66/1.86            != (k1_tarski @ sk_C_2)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['42', '43'])).
% 1.66/1.86  thf('45', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 1.66/1.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['27', '28'])).
% 1.66/1.86  thf('46', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('47', plain,
% 1.66/1.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.66/1.86          | ~ (v2_tex_2 @ X27 @ X28)
% 1.66/1.86          | (v4_pre_topc @ (sk_D @ X29 @ X27 @ X28) @ X28)
% 1.66/1.86          | ~ (r1_tarski @ X29 @ X27)
% 1.66/1.86          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.66/1.86          | ~ (l1_pre_topc @ X28))),
% 1.66/1.86      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.66/1.86  thf('48', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (l1_pre_topc @ sk_A)
% 1.66/1.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.66/1.86          | (v4_pre_topc @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ sk_A)
% 1.66/1.86          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['46', '47'])).
% 1.66/1.86  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('50', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('51', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.66/1.86          | (v4_pre_topc @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.66/1.86  thf('52', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A) @ sk_A)
% 1.66/1.86        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['45', '51'])).
% 1.66/1.86  thf('53', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 1.66/1.86      inference('demod', [status(thm)], ['39', '40'])).
% 1.66/1.86  thf('54', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A) @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['52', '53'])).
% 1.66/1.86  thf('55', plain,
% 1.66/1.86      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 1.66/1.86          (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A))
% 1.66/1.86          != (k1_tarski @ sk_C_2))
% 1.66/1.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('clc', [status(thm)], ['44', '54'])).
% 1.66/1.86  thf('56', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 1.66/1.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['27', '28'])).
% 1.66/1.86  thf('57', plain,
% 1.66/1.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('58', plain,
% 1.66/1.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.66/1.86          | ~ (v2_tex_2 @ X27 @ X28)
% 1.66/1.86          | ((k9_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 1.66/1.86              (sk_D @ X29 @ X27 @ X28)) = (X29))
% 1.66/1.86          | ~ (r1_tarski @ X29 @ X27)
% 1.66/1.86          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.66/1.86          | ~ (l1_pre_topc @ X28))),
% 1.66/1.86      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.66/1.86  thf('59', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (l1_pre_topc @ sk_A)
% 1.66/1.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.66/1.86          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 1.66/1.86              (sk_D @ X0 @ sk_B_1 @ sk_A)) = (X0))
% 1.66/1.86          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['57', '58'])).
% 1.66/1.86  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('61', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('62', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.66/1.86          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.66/1.86          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 1.66/1.86              (sk_D @ X0 @ sk_B_1 @ sk_A)) = (X0)))),
% 1.66/1.86      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.66/1.86  thf('63', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 1.66/1.86            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A))
% 1.66/1.86            = (k1_tarski @ sk_C_2))
% 1.66/1.86        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['56', '62'])).
% 1.66/1.86  thf('64', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 1.66/1.86      inference('demod', [status(thm)], ['39', '40'])).
% 1.66/1.86  thf('65', plain,
% 1.66/1.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.66/1.86        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 1.66/1.86            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B_1 @ sk_A))
% 1.66/1.86            = (k1_tarski @ sk_C_2)))),
% 1.66/1.86      inference('demod', [status(thm)], ['63', '64'])).
% 1.66/1.86  thf('66', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.66/1.86      inference('clc', [status(thm)], ['55', '65'])).
% 1.66/1.86  thf('67', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 1.66/1.86      inference('demod', [status(thm)], ['13', '66'])).
% 1.66/1.86  thf('68', plain, ($false), inference('sup-', [status(thm)], ['10', '67'])).
% 1.66/1.86  
% 1.66/1.86  % SZS output end Refutation
% 1.66/1.86  
% 1.66/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
