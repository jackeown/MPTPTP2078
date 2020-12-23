%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D6wuBMKBv9

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:31 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 175 expanded)
%              Number of leaves         :   29 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  611 (1341 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X26 @ X27 ) @ X26 )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('23',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('36',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X27 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ X29 )
       != ( sk_C_1 @ X26 @ X27 ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ X2 )
       != ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v4_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
       != ( sk_C_1 @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ( k1_xboole_0
       != ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ( k1_xboole_0
       != ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['4','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D6wuBMKBv9
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.15/1.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.34  % Solved by: fo/fo7.sh
% 1.15/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.34  % done 1236 iterations in 0.899s
% 1.15/1.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.34  % SZS output start Refutation
% 1.15/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.34  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.15/1.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.15/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.15/1.34  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.15/1.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.15/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.34  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.15/1.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.15/1.34  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.15/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.34  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.15/1.34  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.15/1.34  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.15/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.34  thf(t35_tex_2, conjecture,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.15/1.34       ( ![B:$i]:
% 1.15/1.34         ( ( ( v1_xboole_0 @ B ) & 
% 1.15/1.34             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.15/1.34           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.34    (~( ![A:$i]:
% 1.15/1.34        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.15/1.34            ( l1_pre_topc @ A ) ) =>
% 1.15/1.34          ( ![B:$i]:
% 1.15/1.34            ( ( ( v1_xboole_0 @ B ) & 
% 1.15/1.34                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.15/1.34              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 1.15/1.34    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 1.15/1.34  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(l13_xboole_0, axiom,
% 1.15/1.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.15/1.34  thf('2', plain,
% 1.15/1.34      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.15/1.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.15/1.34  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['1', '2'])).
% 1.15/1.34  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.15/1.34      inference('demod', [status(thm)], ['0', '3'])).
% 1.15/1.34  thf(d3_tarski, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( r1_tarski @ A @ B ) <=>
% 1.15/1.34       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.15/1.34  thf('5', plain,
% 1.15/1.34      (![X4 : $i, X6 : $i]:
% 1.15/1.34         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.15/1.34      inference('cnf', [status(esa)], [d3_tarski])).
% 1.15/1.34  thf(d1_xboole_0, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.15/1.34  thf('6', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.15/1.34  thf('7', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf(t3_subset, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.15/1.34  thf('8', plain,
% 1.15/1.34      (![X18 : $i, X20 : $i]:
% 1.15/1.34         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.34  thf('9', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['7', '8'])).
% 1.15/1.34  thf(d6_tex_2, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( l1_pre_topc @ A ) =>
% 1.15/1.34       ( ![B:$i]:
% 1.15/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.34           ( ( v2_tex_2 @ B @ A ) <=>
% 1.15/1.34             ( ![C:$i]:
% 1.15/1.34               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.34                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.15/1.34                      ( ![D:$i]:
% 1.15/1.34                        ( ( m1_subset_1 @
% 1.15/1.34                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.34                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.15/1.34                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.15/1.34                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.15/1.34  thf('10', plain,
% 1.15/1.34      (![X26 : $i, X27 : $i]:
% 1.15/1.34         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.15/1.34          | (r1_tarski @ (sk_C_1 @ X26 @ X27) @ X26)
% 1.15/1.34          | (v2_tex_2 @ X26 @ X27)
% 1.15/1.34          | ~ (l1_pre_topc @ X27))),
% 1.15/1.34      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.15/1.34  thf('11', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X1)
% 1.15/1.34          | ~ (l1_pre_topc @ X0)
% 1.15/1.34          | (v2_tex_2 @ X1 @ X0)
% 1.15/1.34          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['9', '10'])).
% 1.15/1.34  thf(t4_subset_1, axiom,
% 1.15/1.34    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.15/1.34  thf('12', plain,
% 1.15/1.34      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 1.15/1.34      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.15/1.34  thf('13', plain,
% 1.15/1.34      (![X18 : $i, X19 : $i]:
% 1.15/1.34         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.34  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.15/1.34      inference('sup-', [status(thm)], ['12', '13'])).
% 1.15/1.34  thf(d10_xboole_0, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.34  thf('15', plain,
% 1.15/1.34      (![X8 : $i, X10 : $i]:
% 1.15/1.34         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.15/1.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.34  thf('16', plain,
% 1.15/1.34      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['14', '15'])).
% 1.15/1.34  thf('17', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.15/1.34          | ~ (l1_pre_topc @ X0)
% 1.15/1.34          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.34          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['11', '16'])).
% 1.15/1.34  thf('18', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('19', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['1', '2'])).
% 1.15/1.34  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.34  thf('21', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.15/1.34          | ~ (l1_pre_topc @ X0)
% 1.15/1.34          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['17', '20'])).
% 1.15/1.34  thf('22', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.15/1.34      inference('demod', [status(thm)], ['0', '3'])).
% 1.15/1.34  thf('23', plain,
% 1.15/1.34      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 1.15/1.34        | ~ (l1_pre_topc @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.15/1.34  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('25', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['23', '24'])).
% 1.15/1.34  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('27', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['7', '8'])).
% 1.15/1.34  thf(cc2_pre_topc, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.15/1.34       ( ![B:$i]:
% 1.15/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.15/1.34           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 1.15/1.34  thf('28', plain,
% 1.15/1.34      (![X24 : $i, X25 : $i]:
% 1.15/1.34         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.15/1.34          | (v4_pre_topc @ X24 @ X25)
% 1.15/1.34          | ~ (v1_xboole_0 @ X24)
% 1.15/1.34          | ~ (l1_pre_topc @ X25)
% 1.15/1.34          | ~ (v2_pre_topc @ X25))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 1.15/1.34  thf('29', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X1)
% 1.15/1.34          | ~ (v2_pre_topc @ X0)
% 1.15/1.34          | ~ (l1_pre_topc @ X0)
% 1.15/1.34          | ~ (v1_xboole_0 @ X1)
% 1.15/1.34          | (v4_pre_topc @ X1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['27', '28'])).
% 1.15/1.34  thf('30', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((v4_pre_topc @ X1 @ X0)
% 1.15/1.34          | ~ (l1_pre_topc @ X0)
% 1.15/1.34          | ~ (v2_pre_topc @ X0)
% 1.15/1.34          | ~ (v1_xboole_0 @ X1))),
% 1.15/1.34      inference('simplify', [status(thm)], ['29'])).
% 1.15/1.34  thf('31', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X0)
% 1.15/1.34          | ~ (v2_pre_topc @ sk_A)
% 1.15/1.34          | (v4_pre_topc @ X0 @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['26', '30'])).
% 1.15/1.34  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('33', plain,
% 1.15/1.34      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['31', '32'])).
% 1.15/1.34  thf('34', plain,
% 1.15/1.34      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 1.15/1.34      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.15/1.34  thf('35', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['7', '8'])).
% 1.15/1.34  thf('36', plain,
% 1.15/1.34      (![X26 : $i, X27 : $i, X29 : $i]:
% 1.15/1.34         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.15/1.34          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.15/1.34          | ~ (v4_pre_topc @ X29 @ X27)
% 1.15/1.34          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X26 @ X29)
% 1.15/1.34              != (sk_C_1 @ X26 @ X27))
% 1.15/1.34          | (v2_tex_2 @ X26 @ X27)
% 1.15/1.34          | ~ (l1_pre_topc @ X27))),
% 1.15/1.34      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.15/1.34  thf('37', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X1)
% 1.15/1.34          | ~ (l1_pre_topc @ X0)
% 1.15/1.34          | (v2_tex_2 @ X1 @ X0)
% 1.15/1.34          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ X2) != (sk_C_1 @ X1 @ X0))
% 1.15/1.34          | ~ (v4_pre_topc @ X2 @ X0)
% 1.15/1.34          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.15/1.34      inference('sup-', [status(thm)], ['35', '36'])).
% 1.15/1.34  thf('38', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 1.15/1.34          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0)
% 1.15/1.34              != (sk_C_1 @ X1 @ X0))
% 1.15/1.34          | (v2_tex_2 @ X1 @ X0)
% 1.15/1.34          | ~ (l1_pre_topc @ X0)
% 1.15/1.34          | ~ (v1_xboole_0 @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['34', '37'])).
% 1.15/1.34  thf('39', plain,
% 1.15/1.34      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 1.15/1.34      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.15/1.34  thf(redefinition_k9_subset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.34       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.15/1.34  thf('40', plain,
% 1.15/1.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.15/1.34         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 1.15/1.34          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.15/1.34  thf('41', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 1.15/1.34           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['39', '40'])).
% 1.15/1.34  thf('42', plain,
% 1.15/1.34      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.15/1.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.34  thf('43', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.15/1.34      inference('simplify', [status(thm)], ['42'])).
% 1.15/1.34  thf('44', plain,
% 1.15/1.34      (![X18 : $i, X20 : $i]:
% 1.15/1.34         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.34  thf('45', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['43', '44'])).
% 1.15/1.34  thf(dt_k9_subset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.34       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.15/1.34  thf('46', plain,
% 1.15/1.34      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.34         ((m1_subset_1 @ (k9_subset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 1.15/1.34          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11)))),
% 1.15/1.34      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 1.15/1.34  thf('47', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['45', '46'])).
% 1.15/1.34  thf('48', plain,
% 1.15/1.34      (![X18 : $i, X19 : $i]:
% 1.15/1.34         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.34  thf('49', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 1.15/1.34      inference('sup-', [status(thm)], ['47', '48'])).
% 1.15/1.34  thf('50', plain,
% 1.15/1.34      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['14', '15'])).
% 1.15/1.34  thf('51', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['49', '50'])).
% 1.15/1.34  thf('52', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['43', '44'])).
% 1.15/1.34  thf('53', plain,
% 1.15/1.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.15/1.34         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 1.15/1.34          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.15/1.34  thf('54', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['52', '53'])).
% 1.15/1.34  thf('55', plain,
% 1.15/1.35      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['51', '54'])).
% 1.15/1.35  thf('56', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['41', '55'])).
% 1.15/1.35  thf('57', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 1.15/1.35          | ((k1_xboole_0) != (sk_C_1 @ X1 @ X0))
% 1.15/1.35          | (v2_tex_2 @ X1 @ X0)
% 1.15/1.35          | ~ (l1_pre_topc @ X0)
% 1.15/1.35          | ~ (v1_xboole_0 @ X1))),
% 1.15/1.35      inference('demod', [status(thm)], ['38', '56'])).
% 1.15/1.35  thf('58', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.35          | ~ (v1_xboole_0 @ X0)
% 1.15/1.35          | ~ (l1_pre_topc @ sk_A)
% 1.15/1.35          | (v2_tex_2 @ X0 @ sk_A)
% 1.15/1.35          | ((k1_xboole_0) != (sk_C_1 @ X0 @ sk_A)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['33', '57'])).
% 1.15/1.35  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.35      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.35  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('61', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (~ (v1_xboole_0 @ X0)
% 1.15/1.35          | (v2_tex_2 @ X0 @ sk_A)
% 1.15/1.35          | ((k1_xboole_0) != (sk_C_1 @ X0 @ sk_A)))),
% 1.15/1.35      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.15/1.35  thf('62', plain,
% 1.15/1.35      ((((k1_xboole_0) != (k1_xboole_0))
% 1.15/1.35        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 1.15/1.35        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['25', '61'])).
% 1.15/1.35  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.35      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.35  thf('64', plain,
% 1.15/1.35      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['62', '63'])).
% 1.15/1.35  thf('65', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.15/1.35      inference('simplify', [status(thm)], ['64'])).
% 1.15/1.35  thf('66', plain, ($false), inference('demod', [status(thm)], ['4', '65'])).
% 1.15/1.35  
% 1.15/1.35  % SZS output end Refutation
% 1.15/1.35  
% 1.15/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
