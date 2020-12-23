%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zAE3AbCUTf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:29 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 124 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  547 ( 899 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
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

thf('17',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X24 )
       != ( sk_C_1 @ X21 @ X22 ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X21 @ X22 ) @ X21 )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43','55'])).

thf('57',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zAE3AbCUTf
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 1045 iterations in 0.796s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.05/1.25  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.05/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.25  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.05/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.05/1.25  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.05/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.05/1.25  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.05/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(t35_tex_2, conjecture,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( ( v1_xboole_0 @ B ) & 
% 1.05/1.25             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.25           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.25    (~( ![A:$i]:
% 1.05/1.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.05/1.25            ( l1_pre_topc @ A ) ) =>
% 1.05/1.25          ( ![B:$i]:
% 1.05/1.25            ( ( ( v1_xboole_0 @ B ) & 
% 1.05/1.25                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.25              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 1.05/1.25  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(l13_xboole_0, axiom,
% 1.05/1.25    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.25  thf('2', plain,
% 1.05/1.25      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.05/1.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.25  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.05/1.25  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.05/1.25      inference('demod', [status(thm)], ['0', '3'])).
% 1.05/1.25  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('6', plain,
% 1.05/1.25      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.05/1.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.25  thf(t4_subset_1, axiom,
% 1.05/1.25    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.05/1.25  thf('7', plain,
% 1.05/1.25      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['6', '7'])).
% 1.05/1.25  thf(cc1_tops_1, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 1.05/1.25  thf('9', plain,
% 1.05/1.25      (![X19 : $i, X20 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.05/1.25          | (v3_pre_topc @ X19 @ X20)
% 1.05/1.25          | ~ (v1_xboole_0 @ X19)
% 1.05/1.25          | ~ (l1_pre_topc @ X20)
% 1.05/1.25          | ~ (v2_pre_topc @ X20))),
% 1.05/1.25      inference('cnf', [status(esa)], [cc1_tops_1])).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (v1_xboole_0 @ X1)
% 1.05/1.25          | ~ (v2_pre_topc @ X0)
% 1.05/1.25          | ~ (l1_pre_topc @ X0)
% 1.05/1.25          | ~ (v1_xboole_0 @ X1)
% 1.05/1.25          | (v3_pre_topc @ X1 @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((v3_pre_topc @ X1 @ X0)
% 1.05/1.25          | ~ (l1_pre_topc @ X0)
% 1.05/1.25          | ~ (v2_pre_topc @ X0)
% 1.05/1.25          | ~ (v1_xboole_0 @ X1))),
% 1.05/1.25      inference('simplify', [status(thm)], ['10'])).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (v1_xboole_0 @ X0)
% 1.05/1.25          | ~ (v2_pre_topc @ sk_A)
% 1.05/1.25          | (v3_pre_topc @ X0 @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['5', '11'])).
% 1.05/1.25  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('14', plain,
% 1.05/1.25      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 1.05/1.25      inference('demod', [status(thm)], ['12', '13'])).
% 1.05/1.25  thf('15', plain,
% 1.05/1.25      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.25  thf('16', plain,
% 1.05/1.25      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.25  thf(d5_tex_2, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ( v2_tex_2 @ B @ A ) <=>
% 1.05/1.25             ( ![C:$i]:
% 1.05/1.25               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.05/1.25                      ( ![D:$i]:
% 1.05/1.25                        ( ( m1_subset_1 @
% 1.05/1.25                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 1.05/1.25                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.05/1.25                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.05/1.25  thf('17', plain,
% 1.05/1.25      (![X21 : $i, X22 : $i, X24 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.05/1.25          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.05/1.25          | ~ (v3_pre_topc @ X24 @ X22)
% 1.05/1.25          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X24)
% 1.05/1.25              != (sk_C_1 @ X21 @ X22))
% 1.05/1.25          | (v2_tex_2 @ X21 @ X22)
% 1.05/1.25          | ~ (l1_pre_topc @ X22))),
% 1.05/1.25      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.05/1.25  thf('18', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (l1_pre_topc @ X0)
% 1.05/1.25          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.05/1.25          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 1.05/1.25              != (sk_C_1 @ k1_xboole_0 @ X0))
% 1.05/1.25          | ~ (v3_pre_topc @ X1 @ X0)
% 1.05/1.25          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['16', '17'])).
% 1.05/1.25  thf('19', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 1.05/1.25          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 1.05/1.25              != (sk_C_1 @ k1_xboole_0 @ X0))
% 1.05/1.25          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.05/1.25          | ~ (l1_pre_topc @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['15', '18'])).
% 1.05/1.25  thf('20', plain,
% 1.05/1.25      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.25  thf(redefinition_k9_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.25       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.05/1.25  thf('21', plain,
% 1.05/1.25      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.05/1.25         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 1.05/1.25          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.05/1.25  thf('22', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 1.05/1.25           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['20', '21'])).
% 1.05/1.25  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.05/1.25  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.25  thf(d3_tarski, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( r1_tarski @ A @ B ) <=>
% 1.05/1.25       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.05/1.25  thf('24', plain,
% 1.05/1.25      (![X1 : $i, X3 : $i]:
% 1.05/1.25         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.25  thf('25', plain,
% 1.05/1.25      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.05/1.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.25  thf('26', plain,
% 1.05/1.25      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.25  thf(dt_k9_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.25       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.05/1.25  thf('27', plain,
% 1.05/1.25      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.05/1.25         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 1.05/1.25          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.05/1.25  thf('28', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 1.05/1.25          (k1_zfmisc_1 @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['26', '27'])).
% 1.05/1.25  thf(t5_subset, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.05/1.25          ( v1_xboole_0 @ C ) ) ))).
% 1.05/1.25  thf('29', plain,
% 1.05/1.25      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X16 @ X17)
% 1.05/1.25          | ~ (v1_xboole_0 @ X18)
% 1.05/1.25          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t5_subset])).
% 1.05/1.25  thf('30', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (~ (v1_xboole_0 @ X0)
% 1.05/1.25          | ~ (r2_hidden @ X2 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['28', '29'])).
% 1.05/1.25  thf('31', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 1.05/1.25           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['20', '21'])).
% 1.05/1.25  thf('32', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (~ (v1_xboole_0 @ X0)
% 1.05/1.25          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 1.05/1.25      inference('demod', [status(thm)], ['30', '31'])).
% 1.05/1.25  thf('33', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.05/1.25          | ~ (v1_xboole_0 @ X0)
% 1.05/1.25          | ~ (v1_xboole_0 @ X3))),
% 1.05/1.25      inference('sup-', [status(thm)], ['25', '32'])).
% 1.05/1.25  thf('34', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.25      inference('condensation', [status(thm)], ['33'])).
% 1.05/1.25  thf('35', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['24', '34'])).
% 1.05/1.25  thf(t3_xboole_1, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.25  thf('36', plain,
% 1.05/1.25      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.05/1.25  thf('37', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.25  thf('38', plain,
% 1.05/1.25      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['23', '37'])).
% 1.05/1.25  thf('39', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.25      inference('demod', [status(thm)], ['22', '38'])).
% 1.05/1.25  thf('40', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 1.05/1.25          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 1.05/1.25          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.05/1.25          | ~ (l1_pre_topc @ X0))),
% 1.05/1.25      inference('demod', [status(thm)], ['19', '39'])).
% 1.05/1.25  thf('41', plain,
% 1.05/1.25      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.05/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.05/1.25        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 1.05/1.25        | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['14', '40'])).
% 1.05/1.25  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.25  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('44', plain,
% 1.05/1.25      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 1.05/1.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.25  thf('45', plain,
% 1.05/1.25      (![X21 : $i, X22 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.05/1.25          | (r1_tarski @ (sk_C_1 @ X21 @ X22) @ X21)
% 1.05/1.25          | (v2_tex_2 @ X21 @ X22)
% 1.05/1.25          | ~ (l1_pre_topc @ X22))),
% 1.05/1.25      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.05/1.25  thf('46', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (~ (l1_pre_topc @ X0)
% 1.05/1.25          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.05/1.25          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['44', '45'])).
% 1.05/1.25  thf('47', plain,
% 1.05/1.25      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.05/1.25  thf('48', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.05/1.25          | ~ (l1_pre_topc @ X0)
% 1.05/1.25          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['46', '47'])).
% 1.05/1.25  thf('49', plain,
% 1.05/1.25      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 1.05/1.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.25  thf('50', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.05/1.25      inference('demod', [status(thm)], ['0', '3'])).
% 1.05/1.25  thf('51', plain,
% 1.05/1.25      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.25  thf('52', plain,
% 1.05/1.25      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 1.05/1.25        | ~ (l1_pre_topc @ sk_A)
% 1.05/1.25        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['48', '51'])).
% 1.05/1.25  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.25  thf('55', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 1.05/1.25      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.05/1.25  thf('56', plain,
% 1.05/1.25      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.05/1.25      inference('demod', [status(thm)], ['41', '42', '43', '55'])).
% 1.05/1.25  thf('57', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.05/1.25      inference('simplify', [status(thm)], ['56'])).
% 1.05/1.25  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 1.05/1.25  
% 1.05/1.25  % SZS output end Refutation
% 1.05/1.25  
% 1.05/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
