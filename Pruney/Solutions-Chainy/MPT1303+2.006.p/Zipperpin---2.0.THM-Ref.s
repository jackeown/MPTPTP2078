%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TKprGqGjeN

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:18 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 125 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  613 (1408 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k8_subset_1_type,type,(
    k8_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t21_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k8_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k8_subset_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k8_subset_1 @ X7 @ X6 @ X8 )
        = ( k3_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k8_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v1_tops_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X14 @ X13 )
        = X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('20',plain,(
    ! [X14: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) )
      | ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
        = X14 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    ! [X14: $i] :
      ( ( k8_setfam_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k8_subset_1 @ X7 @ X6 @ X8 )
        = ( k3_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_subset_1 @ X0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','22'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k8_subset_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k8_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_tops_2 @ X20 @ X21 )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v3_pre_topc @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X20 @ X21 ) @ X21 )
      | ( v1_tops_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(clc,[status(thm)],['43','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['4','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TKprGqGjeN
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.87  % Solved by: fo/fo7.sh
% 0.69/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.87  % done 840 iterations in 0.428s
% 0.69/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.87  % SZS output start Refutation
% 0.69/0.87  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.69/0.87  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.69/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.87  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.69/0.87  thf(k8_subset_1_type, type, k8_subset_1: $i > $i > $i > $i).
% 0.69/0.87  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.69/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.69/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.87  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.69/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(t21_tops_2, conjecture,
% 0.69/0.87    (![A:$i]:
% 0.69/0.87     ( ( l1_pre_topc @ A ) =>
% 0.69/0.87       ( ![B:$i]:
% 0.69/0.87         ( ( m1_subset_1 @
% 0.69/0.87             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.87           ( ![C:$i]:
% 0.69/0.87             ( ( m1_subset_1 @
% 0.69/0.87                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.87               ( ( v1_tops_2 @ B @ A ) =>
% 0.69/0.87                 ( v1_tops_2 @
% 0.69/0.87                   ( k9_subset_1 @
% 0.69/0.87                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.69/0.87                   A ) ) ) ) ) ) ))).
% 0.69/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.87    (~( ![A:$i]:
% 0.69/0.87        ( ( l1_pre_topc @ A ) =>
% 0.69/0.87          ( ![B:$i]:
% 0.69/0.87            ( ( m1_subset_1 @
% 0.69/0.87                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.87              ( ![C:$i]:
% 0.69/0.87                ( ( m1_subset_1 @
% 0.69/0.87                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.87                  ( ( v1_tops_2 @ B @ A ) =>
% 0.69/0.87                    ( v1_tops_2 @
% 0.69/0.87                      ( k9_subset_1 @
% 0.69/0.87                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.69/0.87                      A ) ) ) ) ) ) ) )),
% 0.69/0.87    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 0.69/0.87  thf('0', plain,
% 0.69/0.87      (~ (v1_tops_2 @ 
% 0.69/0.87          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.69/0.87          sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('1', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_C_1 @ 
% 0.69/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(redefinition_k9_subset_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.87       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.69/0.87  thf('2', plain,
% 0.69/0.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.69/0.87         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.69/0.87          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.69/0.87      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.69/0.87  thf('3', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C_1)
% 0.69/0.87           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.69/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.87  thf('4', plain, (~ (v1_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.69/0.87      inference('demod', [status(thm)], ['0', '3'])).
% 0.69/0.87  thf('5', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ 
% 0.69/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(dt_k8_subset_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.87       ( m1_subset_1 @ ( k8_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.87  thf('6', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.87          | (m1_subset_1 @ (k8_subset_1 @ X1 @ X0 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 0.69/0.87      inference('cnf', [status(esa)], [dt_k8_subset_1])).
% 0.69/0.87  thf('7', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (m1_subset_1 @ 
% 0.69/0.87          (k8_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 0.69/0.87          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.87  thf('8', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ 
% 0.69/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(redefinition_k8_subset_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.87       ( ( k8_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.69/0.87  thf('9', plain,
% 0.69/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.69/0.87          | ((k8_subset_1 @ X7 @ X6 @ X8) = (k3_xboole_0 @ X6 @ X8)))),
% 0.69/0.87      inference('cnf', [status(esa)], [redefinition_k8_subset_1])).
% 0.69/0.87  thf('10', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((k8_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.69/0.87           = (k3_xboole_0 @ sk_B @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.87  thf('11', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.69/0.87          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('demod', [status(thm)], ['7', '10'])).
% 0.69/0.87  thf(d1_tops_2, axiom,
% 0.69/0.87    (![A:$i]:
% 0.69/0.87     ( ( l1_pre_topc @ A ) =>
% 0.69/0.87       ( ![B:$i]:
% 0.69/0.87         ( ( m1_subset_1 @
% 0.69/0.87             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.87           ( ( v1_tops_2 @ B @ A ) <=>
% 0.69/0.87             ( ![C:$i]:
% 0.69/0.87               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.87                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.69/0.87  thf('12', plain,
% 0.69/0.87      (![X20 : $i, X21 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X20 @ 
% 0.69/0.87             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.69/0.87          | (r2_hidden @ (sk_C @ X20 @ X21) @ X20)
% 0.69/0.87          | (v1_tops_2 @ X20 @ X21)
% 0.69/0.87          | ~ (l1_pre_topc @ X21))),
% 0.69/0.87      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.69/0.87  thf('13', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (~ (l1_pre_topc @ sk_A)
% 0.69/0.87          | (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.69/0.87          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ 
% 0.69/0.87             (k3_xboole_0 @ sk_B @ X0)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.87  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('15', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.69/0.87          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ 
% 0.69/0.87             (k3_xboole_0 @ sk_B @ X0)))),
% 0.69/0.87      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.87  thf(t4_subset_1, axiom,
% 0.69/0.87    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.69/0.87  thf('16', plain,
% 0.69/0.87      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.69/0.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.87  thf(dt_k8_setfam_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.87       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.87  thf('17', plain,
% 0.69/0.87      (![X15 : $i, X16 : $i]:
% 0.69/0.87         ((m1_subset_1 @ (k8_setfam_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.69/0.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.69/0.87      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.69/0.87  thf('18', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (m1_subset_1 @ (k8_setfam_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.87  thf(d10_setfam_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.87       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.69/0.87           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.69/0.87         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.69/0.87  thf('19', plain,
% 0.69/0.87      (![X13 : $i, X14 : $i]:
% 0.69/0.87         (((X13) != (k1_xboole_0))
% 0.69/0.87          | ((k8_setfam_1 @ X14 @ X13) = (X14))
% 0.69/0.87          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.69/0.87      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.69/0.87  thf('20', plain,
% 0.69/0.87      (![X14 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14)))
% 0.69/0.87          | ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['19'])).
% 0.69/0.87  thf('21', plain,
% 0.69/0.87      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.69/0.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.69/0.87  thf('22', plain, (![X14 : $i]: ((k8_setfam_1 @ X14 @ k1_xboole_0) = (X14))),
% 0.69/0.87      inference('demod', [status(thm)], ['20', '21'])).
% 0.69/0.87  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.87      inference('demod', [status(thm)], ['18', '22'])).
% 0.69/0.87  thf('24', plain,
% 0.69/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.69/0.87          | ((k8_subset_1 @ X7 @ X6 @ X8) = (k3_xboole_0 @ X6 @ X8)))),
% 0.69/0.87      inference('cnf', [status(esa)], [redefinition_k8_subset_1])).
% 0.69/0.87  thf('25', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((k8_subset_1 @ X0 @ X0 @ X1) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('sup-', [status(thm)], ['23', '24'])).
% 0.69/0.87  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.69/0.87      inference('demod', [status(thm)], ['18', '22'])).
% 0.69/0.87  thf('27', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.87          | (m1_subset_1 @ (k8_subset_1 @ X1 @ X0 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 0.69/0.87      inference('cnf', [status(esa)], [dt_k8_subset_1])).
% 0.69/0.87  thf('28', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (m1_subset_1 @ (k8_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.87  thf('29', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.69/0.87      inference('sup+', [status(thm)], ['25', '28'])).
% 0.69/0.87  thf(l3_subset_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.69/0.87  thf('30', plain,
% 0.69/0.87      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X3 @ X4)
% 0.69/0.87          | (r2_hidden @ X3 @ X5)
% 0.69/0.87          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.69/0.87      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.69/0.87  thf('31', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.87  thf('32', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.69/0.87          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_B))),
% 0.69/0.87      inference('sup-', [status(thm)], ['15', '31'])).
% 0.69/0.87  thf('33', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ 
% 0.69/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('34', plain,
% 0.69/0.87      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X20 @ 
% 0.69/0.87             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.69/0.87          | ~ (v1_tops_2 @ X20 @ X21)
% 0.69/0.87          | ~ (r2_hidden @ X22 @ X20)
% 0.69/0.87          | (v3_pre_topc @ X22 @ X21)
% 0.69/0.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.69/0.87          | ~ (l1_pre_topc @ X21))),
% 0.69/0.87      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.69/0.87  thf('35', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (~ (l1_pre_topc @ sk_A)
% 0.69/0.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.87          | (v3_pre_topc @ X0 @ sk_A)
% 0.69/0.87          | ~ (r2_hidden @ X0 @ sk_B)
% 0.69/0.87          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.87  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('37', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('38', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.87          | (v3_pre_topc @ X0 @ sk_A)
% 0.69/0.87          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.69/0.87      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.69/0.87  thf('39', plain,
% 0.69/0.87      ((m1_subset_1 @ sk_B @ 
% 0.69/0.87        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(t4_subset, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.69/0.87       ( m1_subset_1 @ A @ C ) ))).
% 0.69/0.87  thf('40', plain,
% 0.69/0.87      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X17 @ X18)
% 0.69/0.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.69/0.87          | (m1_subset_1 @ X17 @ X19))),
% 0.69/0.87      inference('cnf', [status(esa)], [t4_subset])).
% 0.69/0.87  thf('41', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.87          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.69/0.87      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.87  thf('42', plain,
% 0.69/0.87      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (v3_pre_topc @ X0 @ sk_A))),
% 0.69/0.87      inference('clc', [status(thm)], ['38', '41'])).
% 0.69/0.87  thf('43', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.69/0.87          | (v3_pre_topc @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['32', '42'])).
% 0.69/0.87  thf('44', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.69/0.87          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.87      inference('demod', [status(thm)], ['7', '10'])).
% 0.69/0.87  thf('45', plain,
% 0.69/0.87      (![X20 : $i, X21 : $i]:
% 0.69/0.87         (~ (m1_subset_1 @ X20 @ 
% 0.69/0.87             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.69/0.87          | ~ (v3_pre_topc @ (sk_C @ X20 @ X21) @ X21)
% 0.69/0.87          | (v1_tops_2 @ X20 @ X21)
% 0.69/0.87          | ~ (l1_pre_topc @ X21))),
% 0.69/0.87      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.69/0.87  thf('46', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         (~ (l1_pre_topc @ sk_A)
% 0.69/0.87          | (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.69/0.87          | ~ (v3_pre_topc @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_A))),
% 0.69/0.87      inference('sup-', [status(thm)], ['44', '45'])).
% 0.69/0.87  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('48', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.69/0.87          | ~ (v3_pre_topc @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ sk_A))),
% 0.69/0.87      inference('demod', [status(thm)], ['46', '47'])).
% 0.69/0.87  thf('49', plain,
% 0.69/0.87      (![X0 : $i]: (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.69/0.87      inference('clc', [status(thm)], ['43', '48'])).
% 0.69/0.87  thf('50', plain, ($false), inference('demod', [status(thm)], ['4', '49'])).
% 0.69/0.87  
% 0.69/0.87  % SZS output end Refutation
% 0.69/0.87  
% 0.69/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
