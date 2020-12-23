%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AgBHUgqhGZ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:09 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 133 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  666 (1710 expanded)
%              Number of equality atoms :   32 (  70 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t81_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( v3_pre_topc @ C @ A )
                   => ( ( k2_pre_topc @ A @ C )
                      = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_pre_topc @ X20 @ X21 ) ) )
        = ( k2_pre_topc @ X20 @ ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','15','18'])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ X12 @ X10 )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','40'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
      = sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('46',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('50',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','25','48','49'])).

thf('51',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('53',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AgBHUgqhGZ
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 245 iterations in 0.149s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.43/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.62  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.43/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.43/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.43/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.43/0.62  thf(d3_struct_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X15 : $i]:
% 0.43/0.62         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.62  thf(t81_tops_1, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ( v1_tops_1 @ B @ A ) =>
% 0.43/0.62             ( ![C:$i]:
% 0.43/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62                 ( ( v3_pre_topc @ C @ A ) =>
% 0.43/0.62                   ( ( k2_pre_topc @ A @ C ) =
% 0.43/0.62                     ( k2_pre_topc @
% 0.43/0.62                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62              ( ( v1_tops_1 @ B @ A ) =>
% 0.43/0.62                ( ![C:$i]:
% 0.43/0.62                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62                    ( ( v3_pre_topc @ C @ A ) =>
% 0.43/0.62                      ( ( k2_pre_topc @ A @ C ) =
% 0.43/0.62                        ( k2_pre_topc @
% 0.43/0.62                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t41_tops_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62               ( ( v3_pre_topc @ B @ A ) =>
% 0.43/0.62                 ( ( k2_pre_topc @
% 0.43/0.62                     A @ 
% 0.43/0.62                     ( k9_subset_1 @
% 0.43/0.62                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.43/0.62                   ( k2_pre_topc @
% 0.43/0.62                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.43/0.62          | ~ (v3_pre_topc @ X19 @ X20)
% 0.43/0.62          | ((k2_pre_topc @ X20 @ 
% 0.43/0.62              (k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.43/0.62               (k2_pre_topc @ X20 @ X21)))
% 0.43/0.62              = (k2_pre_topc @ X20 @ 
% 0.43/0.62                 (k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ X21)))
% 0.43/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.43/0.62          | ~ (l1_pre_topc @ X20)
% 0.43/0.62          | ~ (v2_pre_topc @ X20))),
% 0.43/0.62      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.62          | ((k2_pre_topc @ sk_A @ 
% 0.43/0.62              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.43/0.62               (k2_pre_topc @ sk_A @ X0)))
% 0.43/0.62              = (k2_pre_topc @ sk_A @ 
% 0.43/0.62                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 0.43/0.62          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('7', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.62          | ((k2_pre_topc @ sk_A @ 
% 0.43/0.62              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.43/0.62               (k2_pre_topc @ sk_A @ X0)))
% 0.43/0.62              = (k2_pre_topc @ sk_A @ 
% 0.43/0.62                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 0.43/0.62      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (((k2_pre_topc @ sk_A @ 
% 0.43/0.62         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.43/0.62          (k2_pre_topc @ sk_A @ sk_B)))
% 0.43/0.62         = (k2_pre_topc @ sk_A @ 
% 0.43/0.62            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '8'])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d3_tops_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ( v1_tops_1 @ B @ A ) <=>
% 0.43/0.62             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.43/0.62          | ~ (v1_tops_1 @ X17 @ X18)
% 0.43/0.62          | ((k2_pre_topc @ X18 @ X17) = (k2_struct_0 @ X18))
% 0.43/0.62          | ~ (l1_pre_topc @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.43/0.62        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(redefinition_k9_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.43/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.43/0.62           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (((k2_pre_topc @ sk_A @ 
% 0.43/0.62         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.43/0.62         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['9', '15', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      ((((k2_pre_topc @ sk_A @ 
% 0.43/0.62          (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.43/0.62          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))
% 0.43/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup+', [status(thm)], ['0', '19'])).
% 0.43/0.62  thf(dt_k2_subset_1, axiom,
% 0.43/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.43/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.43/0.62  thf('22', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.43/0.62  thf('23', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.43/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X15 : $i]:
% 0.43/0.62         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('28', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf(t7_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ![C:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62           ( ( ![D:$i]:
% 0.43/0.62               ( ( m1_subset_1 @ D @ A ) =>
% 0.43/0.62                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.43/0.62             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.43/0.62          | (r1_tarski @ X12 @ X10)
% 0.43/0.62          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X12)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.43/0.62          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.43/0.62          | (r1_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (r2_hidden @ 
% 0.43/0.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_C @ (u1_struct_0 @ sk_A)) @ sk_C))),
% 0.43/0.62      inference('sup-', [status(thm)], ['27', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(l3_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X4 @ X5)
% 0.43/0.62          | (r2_hidden @ X4 @ X6)
% 0.43/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.43/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (r2_hidden @ 
% 0.43/0.62           (sk_D @ (u1_struct_0 @ sk_A) @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 0.43/0.62           (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['31', '34'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('37', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.43/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.43/0.62          | (r1_tarski @ X12 @ X10)
% 0.43/0.62          | ~ (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X10)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.43/0.62          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.43/0.62          | (r1_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | ~ (r2_hidden @ 
% 0.43/0.62             (sk_D @ (u1_struct_0 @ sk_A) @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 0.43/0.62             (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['36', '39'])).
% 0.43/0.62  thf('41', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('clc', [status(thm)], ['35', '40'])).
% 0.43/0.62  thf(t28_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.62  thf('43', plain, (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 0.43/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      ((((k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)) = (sk_C))
% 0.43/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup+', [status(thm)], ['26', '43'])).
% 0.43/0.62  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_l1_pre_topc, axiom,
% 0.43/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.62  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.43/0.62  thf('48', plain, (((k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)) = (sk_C))),
% 0.43/0.62      inference('demod', [status(thm)], ['44', '47'])).
% 0.43/0.62  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (((k2_pre_topc @ sk_A @ sk_C)
% 0.43/0.62         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['20', '25', '48', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (((k2_pre_topc @ sk_A @ sk_C)
% 0.43/0.62         != (k2_pre_topc @ sk_A @ 
% 0.43/0.62             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.43/0.62           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (((k2_pre_topc @ sk_A @ sk_C)
% 0.43/0.62         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.43/0.62  thf('54', plain, ($false),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['50', '53'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
