%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.guHuoHY43z

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:26 EST 2020

% Result     : Theorem 15.93s
% Output     : Refutation 15.93s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 266 expanded)
%              Number of leaves         :   34 (  97 expanded)
%              Depth                    :   22
%              Number of atoms          :  857 (2194 expanded)
%              Number of equality atoms :   48 ( 102 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( sk_C @ X22 @ X23 ) @ X22 )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('12',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( sk_C @ X1 @ X0 ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ X1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ X0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_tex_2 @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X1 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('62',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X23 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ X25 )
       != ( sk_C @ X22 @ X23 ) )
      | ( v2_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('69',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','76'])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('80',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['83','84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.guHuoHY43z
% 0.17/0.39  % Computer   : n024.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 15:19:21 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 15.93/16.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.93/16.11  % Solved by: fo/fo7.sh
% 15.93/16.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.93/16.11  % done 14784 iterations in 15.608s
% 15.93/16.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.93/16.11  % SZS output start Refutation
% 15.93/16.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.93/16.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 15.93/16.11  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 15.93/16.11  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 15.93/16.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 15.93/16.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 15.93/16.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 15.93/16.11  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 15.93/16.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.93/16.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 15.93/16.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.93/16.11  thf(sk_B_type, type, sk_B: $i).
% 15.93/16.11  thf(sk_A_type, type, sk_A: $i).
% 15.93/16.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 15.93/16.11  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 15.93/16.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.93/16.11  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 15.93/16.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.93/16.11  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 15.93/16.11  thf(fc10_tops_1, axiom,
% 15.93/16.11    (![A:$i]:
% 15.93/16.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 15.93/16.11       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 15.93/16.11  thf('0', plain,
% 15.93/16.11      (![X21 : $i]:
% 15.93/16.11         ((v3_pre_topc @ (k2_struct_0 @ X21) @ X21)
% 15.93/16.11          | ~ (l1_pre_topc @ X21)
% 15.93/16.11          | ~ (v2_pre_topc @ X21))),
% 15.93/16.11      inference('cnf', [status(esa)], [fc10_tops_1])).
% 15.93/16.11  thf(d3_struct_0, axiom,
% 15.93/16.11    (![A:$i]:
% 15.93/16.11     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 15.93/16.11  thf('1', plain,
% 15.93/16.11      (![X19 : $i]:
% 15.93/16.11         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 15.93/16.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 15.93/16.11  thf(dt_k2_subset_1, axiom,
% 15.93/16.11    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 15.93/16.11  thf('2', plain,
% 15.93/16.11      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 15.93/16.12      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 15.93/16.12  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 15.93/16.12  thf('3', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 15.93/16.12      inference('cnf', [status(esa)], [d4_subset_1])).
% 15.93/16.12  thf('4', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 15.93/16.12      inference('demod', [status(thm)], ['2', '3'])).
% 15.93/16.12  thf(l13_xboole_0, axiom,
% 15.93/16.12    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 15.93/16.12  thf('5', plain,
% 15.93/16.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.93/16.12  thf(t4_subset_1, axiom,
% 15.93/16.12    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 15.93/16.12  thf('6', plain,
% 15.93/16.12      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 15.93/16.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.93/16.12  thf(d5_tex_2, axiom,
% 15.93/16.12    (![A:$i]:
% 15.93/16.12     ( ( l1_pre_topc @ A ) =>
% 15.93/16.12       ( ![B:$i]:
% 15.93/16.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.93/16.12           ( ( v2_tex_2 @ B @ A ) <=>
% 15.93/16.12             ( ![C:$i]:
% 15.93/16.12               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.93/16.12                 ( ~( ( r1_tarski @ C @ B ) & 
% 15.93/16.12                      ( ![D:$i]:
% 15.93/16.12                        ( ( m1_subset_1 @
% 15.93/16.12                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.93/16.12                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 15.93/16.12                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 15.93/16.12                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 15.93/16.12  thf('7', plain,
% 15.93/16.12      (![X22 : $i, X23 : $i]:
% 15.93/16.12         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.93/16.12          | (r1_tarski @ (sk_C @ X22 @ X23) @ X22)
% 15.93/16.12          | (v2_tex_2 @ X22 @ X23)
% 15.93/16.12          | ~ (l1_pre_topc @ X23))),
% 15.93/16.12      inference('cnf', [status(esa)], [d5_tex_2])).
% 15.93/16.12  thf('8', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (~ (l1_pre_topc @ X0)
% 15.93/16.12          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 15.93/16.12          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['6', '7'])).
% 15.93/16.12  thf(t3_xboole_1, axiom,
% 15.93/16.12    (![A:$i]:
% 15.93/16.12     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 15.93/16.12  thf('9', plain,
% 15.93/16.12      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 15.93/16.12      inference('cnf', [status(esa)], [t3_xboole_1])).
% 15.93/16.12  thf('10', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 15.93/16.12          | ~ (l1_pre_topc @ X0)
% 15.93/16.12          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 15.93/16.12      inference('sup-', [status(thm)], ['8', '9'])).
% 15.93/16.12  thf('11', plain,
% 15.93/16.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.93/16.12  thf(t35_tex_2, conjecture,
% 15.93/16.12    (![A:$i]:
% 15.93/16.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 15.93/16.12       ( ![B:$i]:
% 15.93/16.12         ( ( ( v1_xboole_0 @ B ) & 
% 15.93/16.12             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.93/16.12           ( v2_tex_2 @ B @ A ) ) ) ))).
% 15.93/16.12  thf(zf_stmt_0, negated_conjecture,
% 15.93/16.12    (~( ![A:$i]:
% 15.93/16.12        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 15.93/16.12            ( l1_pre_topc @ A ) ) =>
% 15.93/16.12          ( ![B:$i]:
% 15.93/16.12            ( ( ( v1_xboole_0 @ B ) & 
% 15.93/16.12                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.93/16.12              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 15.93/16.12    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 15.93/16.12  thf('12', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf('13', plain, ((v1_xboole_0 @ sk_B)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf('14', plain,
% 15.93/16.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.93/16.12  thf('15', plain, (((sk_B) = (k1_xboole_0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['13', '14'])).
% 15.93/16.12  thf('16', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 15.93/16.12      inference('demod', [status(thm)], ['12', '15'])).
% 15.93/16.12  thf('17', plain,
% 15.93/16.12      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['11', '16'])).
% 15.93/16.12  thf('18', plain,
% 15.93/16.12      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 15.93/16.12        | ~ (l1_pre_topc @ sk_A)
% 15.93/16.12        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['10', '17'])).
% 15.93/16.12  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 15.93/16.12  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 15.93/16.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 15.93/16.12  thf('21', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 15.93/16.12      inference('demod', [status(thm)], ['18', '19', '20'])).
% 15.93/16.12  thf('22', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('sup+', [status(thm)], ['5', '21'])).
% 15.93/16.12  thf('23', plain,
% 15.93/16.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.93/16.12  thf('24', plain,
% 15.93/16.12      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 15.93/16.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.93/16.12  thf('25', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('sup+', [status(thm)], ['23', '24'])).
% 15.93/16.12  thf('26', plain,
% 15.93/16.12      (![X22 : $i, X23 : $i]:
% 15.93/16.12         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.93/16.12          | (m1_subset_1 @ (sk_C @ X22 @ X23) @ 
% 15.93/16.12             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.93/16.12          | (v2_tex_2 @ X22 @ X23)
% 15.93/16.12          | ~ (l1_pre_topc @ X23))),
% 15.93/16.12      inference('cnf', [status(esa)], [d5_tex_2])).
% 15.93/16.12  thf('27', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (~ (v1_xboole_0 @ X1)
% 15.93/16.12          | ~ (l1_pre_topc @ X0)
% 15.93/16.12          | (v2_tex_2 @ X1 @ X0)
% 15.93/16.12          | (m1_subset_1 @ (sk_C @ X1 @ X0) @ 
% 15.93/16.12             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 15.93/16.12      inference('sup-', [status(thm)], ['25', '26'])).
% 15.93/16.12  thf(commutativity_k9_subset_1, axiom,
% 15.93/16.12    (![A:$i,B:$i,C:$i]:
% 15.93/16.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 15.93/16.12       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 15.93/16.12  thf('28', plain,
% 15.93/16.12      (![X2 : $i, X3 : $i, X4 : $i]:
% 15.93/16.12         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 15.93/16.12          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 15.93/16.12      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 15.93/16.12  thf('29', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.93/16.12         ((v2_tex_2 @ X1 @ X0)
% 15.93/16.12          | ~ (l1_pre_topc @ X0)
% 15.93/16.12          | ~ (v1_xboole_0 @ X1)
% 15.93/16.12          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ (sk_C @ X1 @ X0))
% 15.93/16.12              = (k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ X1 @ X0) @ X2)))),
% 15.93/16.12      inference('sup-', [status(thm)], ['27', '28'])).
% 15.93/16.12  thf('30', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0)
% 15.93/16.12            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ X1 @ sk_A) @ X0))
% 15.93/16.12          | ~ (v1_xboole_0 @ X1)
% 15.93/16.12          | ~ (v1_xboole_0 @ X1)
% 15.93/16.12          | ~ (l1_pre_topc @ sk_A)
% 15.93/16.12          | (v2_tex_2 @ X1 @ sk_A))),
% 15.93/16.12      inference('sup+', [status(thm)], ['22', '29'])).
% 15.93/16.12  thf('31', plain,
% 15.93/16.12      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 15.93/16.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.93/16.12  thf(redefinition_k9_subset_1, axiom,
% 15.93/16.12    (![A:$i,B:$i,C:$i]:
% 15.93/16.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 15.93/16.12       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 15.93/16.12  thf('32', plain,
% 15.93/16.12      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.93/16.12         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 15.93/16.12          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 15.93/16.12      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 15.93/16.12  thf('33', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 15.93/16.12           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['31', '32'])).
% 15.93/16.12  thf('34', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 15.93/16.12      inference('demod', [status(thm)], ['2', '3'])).
% 15.93/16.12  thf(dt_k9_subset_1, axiom,
% 15.93/16.12    (![A:$i,B:$i,C:$i]:
% 15.93/16.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 15.93/16.12       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 15.93/16.12  thf('35', plain,
% 15.93/16.12      (![X7 : $i, X8 : $i, X9 : $i]:
% 15.93/16.12         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 15.93/16.12          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 15.93/16.12      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 15.93/16.12  thf('36', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['34', '35'])).
% 15.93/16.12  thf(cc1_subset_1, axiom,
% 15.93/16.12    (![A:$i]:
% 15.93/16.12     ( ( v1_xboole_0 @ A ) =>
% 15.93/16.12       ( ![B:$i]:
% 15.93/16.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 15.93/16.12  thf('37', plain,
% 15.93/16.12      (![X14 : $i, X15 : $i]:
% 15.93/16.12         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 15.93/16.12          | (v1_xboole_0 @ X14)
% 15.93/16.12          | ~ (v1_xboole_0 @ X15))),
% 15.93/16.12      inference('cnf', [status(esa)], [cc1_subset_1])).
% 15.93/16.12  thf('38', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k9_subset_1 @ X0 @ X1 @ X0)))),
% 15.93/16.12      inference('sup-', [status(thm)], ['36', '37'])).
% 15.93/16.12  thf('39', plain,
% 15.93/16.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.93/16.12  thf('40', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (~ (v1_xboole_0 @ X0) | ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_xboole_0)))),
% 15.93/16.12      inference('sup-', [status(thm)], ['38', '39'])).
% 15.93/16.12  thf('41', plain,
% 15.93/16.12      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 15.93/16.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.93/16.12  thf('42', plain,
% 15.93/16.12      (![X2 : $i, X3 : $i, X4 : $i]:
% 15.93/16.12         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 15.93/16.12          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 15.93/16.12      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 15.93/16.12  thf('43', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 15.93/16.12           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 15.93/16.12      inference('sup-', [status(thm)], ['41', '42'])).
% 15.93/16.12  thf('44', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (((k1_xboole_0) = (k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 15.93/16.12          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 15.93/16.12      inference('sup+', [status(thm)], ['40', '43'])).
% 15.93/16.12  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 15.93/16.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 15.93/16.12  thf('46', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         ((k1_xboole_0) = (k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 15.93/16.12      inference('demod', [status(thm)], ['44', '45'])).
% 15.93/16.12  thf('47', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 15.93/16.12      inference('demod', [status(thm)], ['2', '3'])).
% 15.93/16.12  thf('48', plain,
% 15.93/16.12      (![X2 : $i, X3 : $i, X4 : $i]:
% 15.93/16.12         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 15.93/16.12          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 15.93/16.12      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 15.93/16.12  thf('49', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 15.93/16.12      inference('sup-', [status(thm)], ['47', '48'])).
% 15.93/16.12  thf('50', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         ((k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.93/16.12      inference('sup+', [status(thm)], ['46', '49'])).
% 15.93/16.12  thf('51', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 15.93/16.12      inference('demod', [status(thm)], ['2', '3'])).
% 15.93/16.12  thf('52', plain,
% 15.93/16.12      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.93/16.12         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 15.93/16.12          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 15.93/16.12      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 15.93/16.12  thf('53', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['51', '52'])).
% 15.93/16.12  thf('54', plain,
% 15.93/16.12      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 15.93/16.12      inference('demod', [status(thm)], ['50', '53'])).
% 15.93/16.12  thf('55', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 15.93/16.12      inference('demod', [status(thm)], ['33', '54'])).
% 15.93/16.12  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf('57', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (((k1_xboole_0)
% 15.93/16.12            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ X1 @ sk_A) @ X0))
% 15.93/16.12          | ~ (v1_xboole_0 @ X1)
% 15.93/16.12          | ~ (v1_xboole_0 @ X1)
% 15.93/16.12          | (v2_tex_2 @ X1 @ sk_A))),
% 15.93/16.12      inference('demod', [status(thm)], ['30', '55', '56'])).
% 15.93/16.12  thf('58', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((v2_tex_2 @ X1 @ sk_A)
% 15.93/16.12          | ~ (v1_xboole_0 @ X1)
% 15.93/16.12          | ((k1_xboole_0)
% 15.93/16.12              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ X1 @ sk_A) @ X0)))),
% 15.93/16.12      inference('simplify', [status(thm)], ['57'])).
% 15.93/16.12  thf('59', plain,
% 15.93/16.12      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 15.93/16.12      inference('sup-', [status(thm)], ['11', '16'])).
% 15.93/16.12  thf('60', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (((k1_xboole_0)
% 15.93/16.12            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ X1 @ sk_A) @ X0))
% 15.93/16.12          | ~ (v1_xboole_0 @ X1))),
% 15.93/16.12      inference('clc', [status(thm)], ['58', '59'])).
% 15.93/16.12  thf('61', plain,
% 15.93/16.12      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 15.93/16.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 15.93/16.12  thf('62', plain,
% 15.93/16.12      (![X22 : $i, X23 : $i]:
% 15.93/16.12         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.93/16.12          | (m1_subset_1 @ (sk_C @ X22 @ X23) @ 
% 15.93/16.12             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.93/16.12          | (v2_tex_2 @ X22 @ X23)
% 15.93/16.12          | ~ (l1_pre_topc @ X23))),
% 15.93/16.12      inference('cnf', [status(esa)], [d5_tex_2])).
% 15.93/16.12  thf('63', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (~ (l1_pre_topc @ X0)
% 15.93/16.12          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 15.93/16.12          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 15.93/16.12             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 15.93/16.12      inference('sup-', [status(thm)], ['61', '62'])).
% 15.93/16.12  thf('64', plain,
% 15.93/16.12      (![X22 : $i, X23 : $i, X25 : $i]:
% 15.93/16.12         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.93/16.12          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 15.93/16.12          | ~ (v3_pre_topc @ X25 @ X23)
% 15.93/16.12          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ X25)
% 15.93/16.12              != (sk_C @ X22 @ X23))
% 15.93/16.12          | (v2_tex_2 @ X22 @ X23)
% 15.93/16.12          | ~ (l1_pre_topc @ X23))),
% 15.93/16.12      inference('cnf', [status(esa)], [d5_tex_2])).
% 15.93/16.12  thf('65', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 15.93/16.12          | ~ (l1_pre_topc @ X0)
% 15.93/16.12          | ~ (l1_pre_topc @ X0)
% 15.93/16.12          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 15.93/16.12          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 15.93/16.12              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 15.93/16.12          | ~ (v3_pre_topc @ X1 @ X0)
% 15.93/16.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 15.93/16.12      inference('sup-', [status(thm)], ['63', '64'])).
% 15.93/16.12  thf('66', plain,
% 15.93/16.12      (![X0 : $i, X1 : $i]:
% 15.93/16.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 15.93/16.12          | ~ (v3_pre_topc @ X1 @ X0)
% 15.93/16.12          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 15.93/16.12              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 15.93/16.12          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 15.93/16.12          | ~ (l1_pre_topc @ X0)
% 15.93/16.12          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 15.93/16.12      inference('simplify', [status(thm)], ['65'])).
% 15.93/16.12  thf('67', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (((k1_xboole_0) != (sk_C @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))
% 15.93/16.12          | ~ (v1_xboole_0 @ k1_xboole_0)
% 15.93/16.12          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 15.93/16.12          | ~ (l1_pre_topc @ sk_A)
% 15.93/16.12          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 15.93/16.12          | ~ (v3_pre_topc @ X0 @ sk_A)
% 15.93/16.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 15.93/16.12      inference('sup-', [status(thm)], ['60', '66'])).
% 15.93/16.12  thf('68', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 15.93/16.12      inference('demod', [status(thm)], ['18', '19', '20'])).
% 15.93/16.12  thf('69', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 15.93/16.12      inference('demod', [status(thm)], ['18', '19', '20'])).
% 15.93/16.12  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 15.93/16.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 15.93/16.12  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf('72', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 15.93/16.12      inference('demod', [status(thm)], ['18', '19', '20'])).
% 15.93/16.12  thf('73', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (((k1_xboole_0) != (k1_xboole_0))
% 15.93/16.12          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 15.93/16.12          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 15.93/16.12          | ~ (v3_pre_topc @ X0 @ sk_A)
% 15.93/16.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 15.93/16.12      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '72'])).
% 15.93/16.12  thf('74', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.93/16.12          | ~ (v3_pre_topc @ X0 @ sk_A)
% 15.93/16.12          | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 15.93/16.12      inference('simplify', [status(thm)], ['73'])).
% 15.93/16.12  thf('75', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 15.93/16.12      inference('demod', [status(thm)], ['12', '15'])).
% 15.93/16.12  thf('76', plain,
% 15.93/16.12      (![X0 : $i]:
% 15.93/16.12         (~ (v3_pre_topc @ X0 @ sk_A)
% 15.93/16.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 15.93/16.12      inference('clc', [status(thm)], ['74', '75'])).
% 15.93/16.12  thf('77', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 15.93/16.12      inference('sup-', [status(thm)], ['4', '76'])).
% 15.93/16.12  thf('78', plain,
% 15.93/16.12      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 15.93/16.12      inference('sup-', [status(thm)], ['1', '77'])).
% 15.93/16.12  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf(dt_l1_pre_topc, axiom,
% 15.93/16.12    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 15.93/16.12  thf('80', plain,
% 15.93/16.12      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 15.93/16.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 15.93/16.12  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 15.93/16.12      inference('sup-', [status(thm)], ['79', '80'])).
% 15.93/16.12  thf('82', plain, (~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)),
% 15.93/16.12      inference('demod', [status(thm)], ['78', '81'])).
% 15.93/16.12  thf('83', plain, ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 15.93/16.12      inference('sup-', [status(thm)], ['0', '82'])).
% 15.93/16.12  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 15.93/16.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.93/16.12  thf('86', plain, ($false),
% 15.93/16.12      inference('demod', [status(thm)], ['83', '84', '85'])).
% 15.93/16.12  
% 15.93/16.12  % SZS output end Refutation
% 15.93/16.12  
% 15.93/16.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
