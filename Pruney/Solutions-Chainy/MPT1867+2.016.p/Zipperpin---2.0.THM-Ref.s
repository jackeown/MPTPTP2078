%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQ4wwancl8

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:28 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 136 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  645 (1021 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( sk_C @ X23 @ X24 ) @ X23 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_pre_topc @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('30',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 )
       != ( sk_C @ X23 @ X24 ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ X2 )
       != ( sk_C @ X1 @ X0 ) )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
       != ( sk_C @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference('simplify_reflect+',[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['4','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bQ4wwancl8
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 1007 iterations in 0.817s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.28  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.06/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.28  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.06/1.28  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.06/1.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.28  thf(t35_tex_2, conjecture,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( v1_xboole_0 @ B ) & 
% 1.06/1.28             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.28           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i]:
% 1.06/1.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.28            ( l1_pre_topc @ A ) ) =>
% 1.06/1.28          ( ![B:$i]:
% 1.06/1.28            ( ( ( v1_xboole_0 @ B ) & 
% 1.06/1.28                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.28              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 1.06/1.28  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(l13_xboole_0, axiom,
% 1.06/1.28    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.06/1.28  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.28  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.06/1.28      inference('demod', [status(thm)], ['0', '3'])).
% 1.06/1.28  thf('5', plain,
% 1.06/1.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.06/1.28  thf(t4_subset_1, axiom,
% 1.06/1.28    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.06/1.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.28  thf('7', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup+', [status(thm)], ['5', '6'])).
% 1.06/1.28  thf(d5_tex_2, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( l1_pre_topc @ A ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28           ( ( v2_tex_2 @ B @ A ) <=>
% 1.06/1.28             ( ![C:$i]:
% 1.06/1.28               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.06/1.28                      ( ![D:$i]:
% 1.06/1.28                        ( ( m1_subset_1 @
% 1.06/1.28                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 1.06/1.28                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.06/1.28                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      (![X23 : $i, X24 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.28          | (r1_tarski @ (sk_C @ X23 @ X24) @ X23)
% 1.06/1.28          | (v2_tex_2 @ X23 @ X24)
% 1.06/1.28          | ~ (l1_pre_topc @ X24))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.06/1.28  thf('9', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ X1)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | (v2_tex_2 @ X1 @ X0)
% 1.06/1.28          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.06/1.28  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.06/1.28  thf('11', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.06/1.28      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.06/1.28  thf('12', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf(d10_xboole_0, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.28  thf('13', plain,
% 1.06/1.28      (![X2 : $i, X4 : $i]:
% 1.06/1.28         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.06/1.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['12', '13'])).
% 1.06/1.28  thf('15', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v2_tex_2 @ X0 @ X1)
% 1.06/1.28          | ~ (l1_pre_topc @ X1)
% 1.06/1.28          | ~ (v1_xboole_0 @ X0)
% 1.06/1.28          | ((sk_C @ X0 @ X1) = (X0))
% 1.06/1.28          | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['9', '14'])).
% 1.06/1.28  thf('16', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (((sk_C @ X0 @ X1) = (X0))
% 1.06/1.28          | ~ (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X1)
% 1.06/1.28          | (v2_tex_2 @ X0 @ X1))),
% 1.06/1.28      inference('simplify', [status(thm)], ['15'])).
% 1.06/1.28  thf('17', plain,
% 1.06/1.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.06/1.28  thf('18', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.06/1.28      inference('demod', [status(thm)], ['0', '3'])).
% 1.06/1.28  thf('19', plain,
% 1.06/1.28      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.28  thf('20', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | ~ (v1_xboole_0 @ X0)
% 1.06/1.28          | ((sk_C @ X0 @ sk_A) = (X0))
% 1.06/1.28          | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['16', '19'])).
% 1.06/1.28  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('22', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ X0)
% 1.06/1.28          | ((sk_C @ X0 @ sk_A) = (X0))
% 1.06/1.28          | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['20', '21'])).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      (![X0 : $i]: (((sk_C @ X0 @ sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['22'])).
% 1.06/1.28  thf('24', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup+', [status(thm)], ['5', '6'])).
% 1.06/1.28  thf(cc1_tops_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.28           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 1.06/1.28  thf('25', plain,
% 1.06/1.28      (![X21 : $i, X22 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.06/1.28          | (v3_pre_topc @ X21 @ X22)
% 1.06/1.28          | ~ (v1_xboole_0 @ X21)
% 1.06/1.28          | ~ (l1_pre_topc @ X22)
% 1.06/1.28          | ~ (v2_pre_topc @ X22))),
% 1.06/1.28      inference('cnf', [status(esa)], [cc1_tops_1])).
% 1.06/1.28  thf('26', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ X1)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X1)
% 1.06/1.28          | (v3_pre_topc @ X1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['24', '25'])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((v3_pre_topc @ X1 @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X1))),
% 1.06/1.28      inference('simplify', [status(thm)], ['26'])).
% 1.06/1.28  thf('28', plain,
% 1.06/1.28      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.06/1.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.28  thf('29', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.28      inference('sup+', [status(thm)], ['5', '6'])).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.28          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.28          | ~ (v3_pre_topc @ X26 @ X24)
% 1.06/1.28          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26)
% 1.06/1.28              != (sk_C @ X23 @ X24))
% 1.06/1.28          | (v2_tex_2 @ X23 @ X24)
% 1.06/1.28          | ~ (l1_pre_topc @ X24))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ X1)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | (v2_tex_2 @ X1 @ X0)
% 1.06/1.28          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ X2) != (sk_C @ X1 @ X0))
% 1.06/1.28          | ~ (v3_pre_topc @ X2 @ X0)
% 1.06/1.28          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.28  thf('32', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 1.06/1.28          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0)
% 1.06/1.28              != (sk_C @ X1 @ X0))
% 1.06/1.28          | (v2_tex_2 @ X1 @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['28', '31'])).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.06/1.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.28  thf(redefinition_k9_subset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.28       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.06/1.28  thf('34', plain,
% 1.06/1.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.06/1.28         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 1.06/1.28          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.06/1.28  thf('35', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 1.06/1.28           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.28  thf('36', plain,
% 1.06/1.28      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.28  thf('37', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.06/1.28      inference('simplify', [status(thm)], ['36'])).
% 1.06/1.28  thf(t3_subset, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.28  thf('38', plain,
% 1.06/1.28      (![X13 : $i, X15 : $i]:
% 1.06/1.28         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.28  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.28  thf(dt_k9_subset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.28       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.06/1.28  thf('40', plain,
% 1.06/1.28      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.06/1.28         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 1.06/1.28          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['39', '40'])).
% 1.06/1.28  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.28  thf('43', plain,
% 1.06/1.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.06/1.28         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 1.06/1.28          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.06/1.28  thf('44', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['42', '43'])).
% 1.06/1.28  thf('45', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['41', '44'])).
% 1.06/1.28  thf('46', plain,
% 1.06/1.28      (![X13 : $i, X14 : $i]:
% 1.06/1.28         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.28  thf('47', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.06/1.28      inference('sup-', [status(thm)], ['45', '46'])).
% 1.06/1.28  thf('48', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.06/1.28      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.06/1.28  thf('49', plain,
% 1.06/1.28      (![X2 : $i, X4 : $i]:
% 1.06/1.28         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.06/1.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.28  thf('50', plain,
% 1.06/1.28      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.28  thf('51', plain,
% 1.06/1.28      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['47', '50'])).
% 1.06/1.28  thf('52', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.28      inference('demod', [status(thm)], ['35', '51'])).
% 1.06/1.28  thf('53', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 1.06/1.28          | ((k1_xboole_0) != (sk_C @ X1 @ X0))
% 1.06/1.28          | (v2_tex_2 @ X1 @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X1))),
% 1.06/1.28      inference('demod', [status(thm)], ['32', '52'])).
% 1.06/1.28  thf('54', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X1)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | (v2_tex_2 @ X1 @ X0)
% 1.06/1.28          | ((k1_xboole_0) != (sk_C @ X1 @ X0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['27', '53'])).
% 1.06/1.28  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.06/1.28  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.28  thf('56', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X1)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | (v2_tex_2 @ X1 @ X0)
% 1.06/1.28          | ((k1_xboole_0) != (sk_C @ X1 @ X0)))),
% 1.06/1.28      inference('demod', [status(thm)], ['54', '55'])).
% 1.06/1.28  thf('57', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (((k1_xboole_0) != (sk_C @ X1 @ X0))
% 1.06/1.28          | (v2_tex_2 @ X1 @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X1)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['56'])).
% 1.06/1.28  thf('58', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k1_xboole_0) != (X0))
% 1.06/1.28          | ~ (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | ~ (v1_xboole_0 @ X0)
% 1.06/1.28          | (v2_tex_2 @ X0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['23', '57'])).
% 1.06/1.28  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('61', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k1_xboole_0) != (X0))
% 1.06/1.28          | ~ (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ X0)
% 1.06/1.28          | (v2_tex_2 @ X0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.06/1.28  thf('62', plain,
% 1.06/1.28      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['61'])).
% 1.06/1.28  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.28  thf('64', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.06/1.28      inference('simplify_reflect+', [status(thm)], ['62', '63'])).
% 1.06/1.28  thf('65', plain, ($false), inference('demod', [status(thm)], ['4', '64'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
