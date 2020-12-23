%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PLvI3a7coD

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:46 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 236 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  615 (2868 expanded)
%              Number of equality atoms :   20 (  69 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t42_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ ( k2_pre_topc @ X18 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( k6_domain_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ ( k6_domain_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k6_domain_1 @ sk_B @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k6_domain_1 @ sk_B @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('52',plain,
    ( ( k6_domain_1 @ sk_B @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['46','52'])).

thf('54',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','53'])).

thf('55',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('57',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('58',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['54','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PLvI3a7coD
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 430 iterations in 0.222s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.65  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.65  thf(t42_tex_2, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v2_tex_2 @ B @ A ) =>
% 0.46/0.65             ( ![C:$i]:
% 0.46/0.65               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65                 ( ( r2_hidden @ C @ B ) =>
% 0.46/0.65                   ( ( k9_subset_1 @
% 0.46/0.65                       ( u1_struct_0 @ A ) @ B @ 
% 0.46/0.65                       ( k2_pre_topc @
% 0.46/0.65                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.46/0.65                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.65            ( l1_pre_topc @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65              ( ( v2_tex_2 @ B @ A ) =>
% 0.46/0.65                ( ![C:$i]:
% 0.46/0.65                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65                    ( ( r2_hidden @ C @ B ) =>
% 0.46/0.65                      ( ( k9_subset_1 @
% 0.46/0.65                          ( u1_struct_0 @ A ) @ B @ 
% 0.46/0.65                          ( k2_pre_topc @
% 0.46/0.65                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.46/0.65                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.46/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_k6_domain_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.65       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X13)
% 0.46/0.65          | ~ (m1_subset_1 @ X14 @ X13)
% 0.46/0.65          | (m1_subset_1 @ (k6_domain_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ 
% 0.46/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.65       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X15)
% 0.46/0.65          | ~ (m1_subset_1 @ X16 @ X15)
% 0.46/0.65          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf('7', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t3_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.65  thf('10', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(d3_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.65          | (r2_hidden @ X0 @ X2)
% 0.46/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '12'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X7 : $i, X9 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.65  thf('19', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf(t5_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X10 @ X11)
% 0.46/0.65          | ~ (v1_xboole_0 @ X12)
% 0.46/0.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('22', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['6', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.46/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['3', '23'])).
% 0.46/0.65  thf('25', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '21'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.46/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('clc', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t41_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v2_tex_2 @ B @ A ) <=>
% 0.46/0.65             ( ![C:$i]:
% 0.46/0.65               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65                 ( ( r1_tarski @ C @ B ) =>
% 0.46/0.65                   ( ( k9_subset_1 @
% 0.46/0.65                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.46/0.65                     ( C ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.65          | ~ (v2_tex_2 @ X17 @ X18)
% 0.46/0.65          | ~ (r1_tarski @ X19 @ X17)
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ 
% 0.46/0.65              (k2_pre_topc @ X18 @ X19)) = (X19))
% 0.46/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.65          | ~ (l1_pre_topc @ X18)
% 0.46/0.65          | ~ (v2_pre_topc @ X18)
% 0.46/0.65          | (v2_struct_0 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.65              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.46/0.65          | ~ (r1_tarski @ X0 @ sk_B)
% 0.46/0.65          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('32', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.65              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.46/0.65          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)
% 0.46/0.65        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.65            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '33'])).
% 0.46/0.65  thf('35', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d2_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X4 @ X5)
% 0.46/0.65          | (m1_subset_1 @ X4 @ X5)
% 0.46/0.65          | (v1_xboole_0 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('37', plain, (((v1_xboole_0 @ sk_B) | (m1_subset_1 @ sk_C_2 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X13)
% 0.46/0.65          | ~ (m1_subset_1 @ X14 @ X13)
% 0.46/0.65          | (m1_subset_1 @ (k6_domain_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B)
% 0.46/0.65        | (m1_subset_1 @ (k6_domain_1 @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))
% 0.46/0.65        | (v1_xboole_0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (((m1_subset_1 @ (k6_domain_1 @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))
% 0.46/0.65        | (v1_xboole_0 @ sk_B))),
% 0.46/0.65      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.65  thf('41', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('43', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      ((m1_subset_1 @ (k6_domain_1 @ sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.46/0.65      inference('clc', [status(thm)], ['40', '43'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.65  thf('46', plain, ((r1_tarski @ (k6_domain_1 @ sk_B @ sk_C_2) @ sk_B)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('47', plain, (((v1_xboole_0 @ sk_B) | (m1_subset_1 @ sk_C_2 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X15)
% 0.46/0.65          | ~ (m1_subset_1 @ X16 @ X15)
% 0.46/0.65          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B)
% 0.46/0.65        | ((k6_domain_1 @ sk_B @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.46/0.65        | (v1_xboole_0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      ((((k6_domain_1 @ sk_B @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.46/0.65        | (v1_xboole_0 @ sk_B))),
% 0.46/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.46/0.65  thf('51', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.65  thf('52', plain, (((k6_domain_1 @ sk_B @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('53', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.46/0.65      inference('demod', [status(thm)], ['46', '52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.65          (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.65         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.46/0.65         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['6', '22'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.46/0.65      inference('clc', [status(thm)], ['6', '22'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.65         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.46/0.65      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.46/0.65  thf('59', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['54', '58'])).
% 0.46/0.65  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
