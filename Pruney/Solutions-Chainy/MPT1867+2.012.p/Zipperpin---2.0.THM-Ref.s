%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.clCGx3ZNzI

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 143 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  557 (1100 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
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

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X26 @ X27 ) @ X26 )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X27 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ X29 )
       != ( sk_C_1 @ X26 @ X27 ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['31','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['4','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.clCGx3ZNzI
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 118 iterations in 0.103s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(t35_tex_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56            ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.20/0.56  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(l13_xboole_0, axiom,
% 0.20/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.56  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.56  thf(t4_subset_1, axiom,
% 0.20/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf(d5_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.56             ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.20/0.56                      ( ![D:$i]:
% 0.20/0.56                        ( ( m1_subset_1 @
% 0.20/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.56                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.56                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X26 : $i, X27 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.56          | (r1_tarski @ (sk_C_1 @ X26 @ X27) @ X26)
% 0.20/0.56          | (v2_tex_2 @ X26 @ X27)
% 0.20/0.56          | ~ (l1_pre_topc @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf(d3_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X4 : $i, X6 : $i]:
% 0.20/0.56         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf(d1_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf(d10_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X8 : $i, X10 : $i]:
% 0.20/0.56         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.56          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.56  thf('14', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.56  thf('18', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('21', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf(cc1_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X24 : $i, X25 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.56          | (v3_pre_topc @ X24 @ X25)
% 0.20/0.56          | ~ (v1_xboole_0 @ X24)
% 0.20/0.56          | ~ (l1_pre_topc @ X25)
% 0.20/0.56          | ~ (v2_pre_topc @ X25))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.56          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X26 : $i, X27 : $i, X29 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.56          | ~ (v3_pre_topc @ X29 @ X27)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X26 @ X29)
% 0.20/0.56              != (sk_C_1 @ X26 @ X27))
% 0.20/0.56          | (v2_tex_2 @ X26 @ X27)
% 0.20/0.56          | ~ (l1_pre_topc @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.20/0.56              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.20/0.56          | ~ (v3_pre_topc @ X1 @ X0)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.56              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.20/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.20/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.20/0.56           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf(dt_k9_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         ((m1_subset_1 @ (k9_subset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 0.20/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 0.20/0.56          (k1_zfmisc_1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.56  thf(t5_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X21 @ X22)
% 0.20/0.56          | ~ (v1_xboole_0 @ X23)
% 0.20/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ X0)
% 0.20/0.56          | ~ (r2_hidden @ X2 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.20/0.56           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ X0)
% 0.20/0.56          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.20/0.56          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ X1)
% 0.20/0.56          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['35', '46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['34', '47'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.20/0.56          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.20/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['31', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '49'])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.20/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '51'])).
% 0.20/0.56  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.56  thf('56', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.56  thf('57', plain, ($false), inference('demod', [status(thm)], ['4', '56'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
