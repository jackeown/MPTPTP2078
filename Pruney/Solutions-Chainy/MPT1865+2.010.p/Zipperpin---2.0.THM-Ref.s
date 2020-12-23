%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8pepBRaM5E

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:22 EST 2020

% Result     : Theorem 33.02s
% Output     : Refutation 33.02s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 658 expanded)
%              Number of leaves         :   25 ( 213 expanded)
%              Depth                    :   24
%              Number of atoms          :  966 (5808 expanded)
%              Number of equality atoms :   23 ( 238 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( sk_D @ X22 @ X20 @ X21 ) )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7
        = ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ ( sk_C @ X7 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X7 @ X4 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('48',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['58'])).

thf('60',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['58'])).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['34','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('71',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','73'])).

thf('75',plain,(
    ! [X24: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X24 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v4_pre_topc @ X24 @ sk_A )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( v4_pre_topc @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','88'])).

thf('90',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('93',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','93'])).

thf('95',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8pepBRaM5E
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 33.02/33.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 33.02/33.24  % Solved by: fo/fo7.sh
% 33.02/33.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.02/33.24  % done 11955 iterations in 32.777s
% 33.02/33.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 33.02/33.24  % SZS output start Refutation
% 33.02/33.24  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 33.02/33.24  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 33.02/33.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 33.02/33.24  thf(sk_C_2_type, type, sk_C_2: $i).
% 33.02/33.24  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 33.02/33.24  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 33.02/33.24  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 33.02/33.24  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 33.02/33.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 33.02/33.24  thf(sk_B_type, type, sk_B: $i).
% 33.02/33.24  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 33.02/33.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 33.02/33.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 33.02/33.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 33.02/33.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 33.02/33.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 33.02/33.24  thf(sk_A_type, type, sk_A: $i).
% 33.02/33.24  thf(t33_tex_2, conjecture,
% 33.02/33.24    (![A:$i]:
% 33.02/33.24     ( ( l1_pre_topc @ A ) =>
% 33.02/33.24       ( ![B:$i]:
% 33.02/33.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.02/33.24           ( ( v2_tex_2 @ B @ A ) =>
% 33.02/33.24             ( ![C:$i]:
% 33.02/33.24               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 33.02/33.24                 ( ~( ( r2_hidden @ C @ B ) & 
% 33.02/33.24                      ( ![D:$i]:
% 33.02/33.24                        ( ( m1_subset_1 @
% 33.02/33.24                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.02/33.24                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 33.02/33.24                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 33.02/33.24                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 33.02/33.24  thf(zf_stmt_0, negated_conjecture,
% 33.02/33.24    (~( ![A:$i]:
% 33.02/33.24        ( ( l1_pre_topc @ A ) =>
% 33.02/33.24          ( ![B:$i]:
% 33.02/33.24            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.02/33.24              ( ( v2_tex_2 @ B @ A ) =>
% 33.02/33.24                ( ![C:$i]:
% 33.02/33.24                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 33.02/33.24                    ( ~( ( r2_hidden @ C @ B ) & 
% 33.02/33.24                         ( ![D:$i]:
% 33.02/33.24                           ( ( m1_subset_1 @
% 33.02/33.24                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.02/33.24                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 33.02/33.24                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 33.02/33.24                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 33.02/33.24    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 33.02/33.24  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf('1', plain,
% 33.02/33.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf(t5_subset, axiom,
% 33.02/33.24    (![A:$i,B:$i,C:$i]:
% 33.02/33.24     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 33.02/33.24          ( v1_xboole_0 @ C ) ) ))).
% 33.02/33.24  thf('2', plain,
% 33.02/33.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.02/33.24         (~ (r2_hidden @ X17 @ X18)
% 33.02/33.24          | ~ (v1_xboole_0 @ X19)
% 33.02/33.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 33.02/33.24      inference('cnf', [status(esa)], [t5_subset])).
% 33.02/33.24  thf('3', plain,
% 33.02/33.24      (![X0 : $i]:
% 33.02/33.24         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 33.02/33.24      inference('sup-', [status(thm)], ['1', '2'])).
% 33.02/33.24  thf('4', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf(t63_subset_1, axiom,
% 33.02/33.24    (![A:$i,B:$i]:
% 33.02/33.24     ( ( r2_hidden @ A @ B ) =>
% 33.02/33.24       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 33.02/33.24  thf('5', plain,
% 33.02/33.24      (![X13 : $i, X14 : $i]:
% 33.02/33.24         ((m1_subset_1 @ (k1_tarski @ X13) @ (k1_zfmisc_1 @ X14))
% 33.02/33.24          | ~ (r2_hidden @ X13 @ X14))),
% 33.02/33.24      inference('cnf', [status(esa)], [t63_subset_1])).
% 33.02/33.24  thf('6', plain,
% 33.02/33.24      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 33.02/33.24      inference('sup-', [status(thm)], ['4', '5'])).
% 33.02/33.24  thf(d2_subset_1, axiom,
% 33.02/33.24    (![A:$i,B:$i]:
% 33.02/33.24     ( ( ( v1_xboole_0 @ A ) =>
% 33.02/33.24         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 33.02/33.24       ( ( ~( v1_xboole_0 @ A ) ) =>
% 33.02/33.24         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 33.02/33.24  thf('7', plain,
% 33.02/33.24      (![X8 : $i, X9 : $i]:
% 33.02/33.24         (~ (m1_subset_1 @ X8 @ X9)
% 33.02/33.24          | (r2_hidden @ X8 @ X9)
% 33.02/33.24          | (v1_xboole_0 @ X9))),
% 33.02/33.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 33.02/33.24  thf('8', plain,
% 33.02/33.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 33.02/33.24        | (r2_hidden @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B)))),
% 33.02/33.24      inference('sup-', [status(thm)], ['6', '7'])).
% 33.02/33.24  thf(d1_zfmisc_1, axiom,
% 33.02/33.24    (![A:$i,B:$i]:
% 33.02/33.24     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 33.02/33.24       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 33.02/33.24  thf('9', plain,
% 33.02/33.24      (![X4 : $i, X5 : $i, X6 : $i]:
% 33.02/33.24         (~ (r2_hidden @ X6 @ X5)
% 33.02/33.24          | (r1_tarski @ X6 @ X4)
% 33.02/33.24          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 33.02/33.24      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 33.02/33.24  thf('10', plain,
% 33.02/33.24      (![X4 : $i, X6 : $i]:
% 33.02/33.24         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 33.02/33.24      inference('simplify', [status(thm)], ['9'])).
% 33.02/33.24  thf('11', plain,
% 33.02/33.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 33.02/33.24        | (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 33.02/33.24      inference('sup-', [status(thm)], ['8', '10'])).
% 33.02/33.24  thf('12', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf('13', plain,
% 33.02/33.24      (![X8 : $i, X9 : $i]:
% 33.02/33.24         (~ (m1_subset_1 @ X8 @ X9)
% 33.02/33.24          | (r2_hidden @ X8 @ X9)
% 33.02/33.24          | (v1_xboole_0 @ X9))),
% 33.02/33.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 33.02/33.24  thf('14', plain,
% 33.02/33.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.24        | (r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.24      inference('sup-', [status(thm)], ['12', '13'])).
% 33.02/33.24  thf('15', plain,
% 33.02/33.24      (![X13 : $i, X14 : $i]:
% 33.02/33.24         ((m1_subset_1 @ (k1_tarski @ X13) @ (k1_zfmisc_1 @ X14))
% 33.02/33.24          | ~ (r2_hidden @ X13 @ X14))),
% 33.02/33.24      inference('cnf', [status(esa)], [t63_subset_1])).
% 33.02/33.24  thf('16', plain,
% 33.02/33.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.24        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 33.02/33.24           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 33.02/33.24      inference('sup-', [status(thm)], ['14', '15'])).
% 33.02/33.24  thf('17', plain,
% 33.02/33.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf(d6_tex_2, axiom,
% 33.02/33.24    (![A:$i]:
% 33.02/33.24     ( ( l1_pre_topc @ A ) =>
% 33.02/33.24       ( ![B:$i]:
% 33.02/33.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.02/33.24           ( ( v2_tex_2 @ B @ A ) <=>
% 33.02/33.24             ( ![C:$i]:
% 33.02/33.24               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.02/33.24                 ( ~( ( r1_tarski @ C @ B ) & 
% 33.02/33.24                      ( ![D:$i]:
% 33.02/33.24                        ( ( m1_subset_1 @
% 33.02/33.24                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 33.02/33.24                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 33.02/33.24                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 33.02/33.24                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 33.02/33.24  thf('18', plain,
% 33.02/33.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 33.02/33.24         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 33.02/33.24          | ~ (v2_tex_2 @ X20 @ X21)
% 33.02/33.24          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 33.02/33.24              (sk_D @ X22 @ X20 @ X21)) = (X22))
% 33.02/33.24          | ~ (r1_tarski @ X22 @ X20)
% 33.02/33.24          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 33.02/33.24          | ~ (l1_pre_topc @ X21))),
% 33.02/33.24      inference('cnf', [status(esa)], [d6_tex_2])).
% 33.02/33.24  thf('19', plain,
% 33.02/33.24      (![X0 : $i]:
% 33.02/33.24         (~ (l1_pre_topc @ sk_A)
% 33.02/33.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.24          | ~ (r1_tarski @ X0 @ sk_B)
% 33.02/33.24          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 33.02/33.24              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 33.02/33.24          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 33.02/33.24      inference('sup-', [status(thm)], ['17', '18'])).
% 33.02/33.24  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf('21', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf('22', plain,
% 33.02/33.24      (![X0 : $i]:
% 33.02/33.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.24          | ~ (r1_tarski @ X0 @ sk_B)
% 33.02/33.24          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 33.02/33.24              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 33.02/33.24      inference('demod', [status(thm)], ['19', '20', '21'])).
% 33.02/33.24  thf('23', plain,
% 33.02/33.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.24        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 33.02/33.24            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 33.02/33.24        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 33.02/33.24      inference('sup-', [status(thm)], ['16', '22'])).
% 33.02/33.24  thf('24', plain,
% 33.02/33.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 33.02/33.24        | (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 33.02/33.24      inference('sup-', [status(thm)], ['8', '10'])).
% 33.02/33.24  thf('25', plain,
% 33.02/33.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.24        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 33.02/33.24           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 33.02/33.24      inference('sup-', [status(thm)], ['14', '15'])).
% 33.02/33.24  thf('26', plain,
% 33.02/33.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf('27', plain,
% 33.02/33.24      (![X20 : $i, X21 : $i, X22 : $i]:
% 33.02/33.24         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 33.02/33.24          | ~ (v2_tex_2 @ X20 @ X21)
% 33.02/33.24          | (m1_subset_1 @ (sk_D @ X22 @ X20 @ X21) @ 
% 33.02/33.24             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 33.02/33.24          | ~ (r1_tarski @ X22 @ X20)
% 33.02/33.24          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 33.02/33.24          | ~ (l1_pre_topc @ X21))),
% 33.02/33.24      inference('cnf', [status(esa)], [d6_tex_2])).
% 33.02/33.24  thf('28', plain,
% 33.02/33.24      (![X0 : $i]:
% 33.02/33.24         (~ (l1_pre_topc @ sk_A)
% 33.02/33.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.24          | ~ (r1_tarski @ X0 @ sk_B)
% 33.02/33.24          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 33.02/33.24             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.24          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 33.02/33.24      inference('sup-', [status(thm)], ['26', '27'])).
% 33.02/33.24  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf('30', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf('31', plain,
% 33.02/33.24      (![X0 : $i]:
% 33.02/33.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.24          | ~ (r1_tarski @ X0 @ sk_B)
% 33.02/33.24          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 33.02/33.24             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 33.02/33.24      inference('demod', [status(thm)], ['28', '29', '30'])).
% 33.02/33.24  thf('32', plain,
% 33.02/33.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.24        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 33.02/33.24           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.24        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 33.02/33.24      inference('sup-', [status(thm)], ['25', '31'])).
% 33.02/33.24  thf('33', plain,
% 33.02/33.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 33.02/33.24        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 33.02/33.24           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.24        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.24      inference('sup-', [status(thm)], ['24', '32'])).
% 33.02/33.24  thf('34', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 33.02/33.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.24  thf(dt_k2_subset_1, axiom,
% 33.02/33.24    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 33.02/33.24  thf('35', plain,
% 33.02/33.24      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 33.02/33.24      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 33.02/33.24  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 33.02/33.24  thf('36', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 33.02/33.24      inference('cnf', [status(esa)], [d4_subset_1])).
% 33.02/33.24  thf('37', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 33.02/33.24      inference('demod', [status(thm)], ['35', '36'])).
% 33.02/33.24  thf('38', plain,
% 33.02/33.24      (![X8 : $i, X9 : $i]:
% 33.02/33.24         (~ (m1_subset_1 @ X8 @ X9)
% 33.02/33.24          | (r2_hidden @ X8 @ X9)
% 33.02/33.24          | (v1_xboole_0 @ X9))),
% 33.02/33.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 33.02/33.24  thf('39', plain,
% 33.02/33.24      (![X0 : $i]:
% 33.02/33.24         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 33.02/33.24          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 33.02/33.24      inference('sup-', [status(thm)], ['37', '38'])).
% 33.02/33.24  thf('40', plain,
% 33.02/33.24      (![X4 : $i, X6 : $i]:
% 33.02/33.24         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 33.02/33.24      inference('simplify', [status(thm)], ['9'])).
% 33.02/33.24  thf('41', plain,
% 33.02/33.24      (![X0 : $i]: ((v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X0 @ X0))),
% 33.02/33.24      inference('sup-', [status(thm)], ['39', '40'])).
% 33.02/33.25  thf('42', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 33.02/33.25      inference('demod', [status(thm)], ['35', '36'])).
% 33.02/33.25  thf('43', plain,
% 33.02/33.25      (![X9 : $i, X10 : $i]:
% 33.02/33.25         (~ (m1_subset_1 @ X10 @ X9)
% 33.02/33.25          | (v1_xboole_0 @ X10)
% 33.02/33.25          | ~ (v1_xboole_0 @ X9))),
% 33.02/33.25      inference('cnf', [status(esa)], [d2_subset_1])).
% 33.02/33.25  thf('44', plain,
% 33.02/33.25      (![X0 : $i]: (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (v1_xboole_0 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['42', '43'])).
% 33.02/33.25  thf('45', plain, (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['41', '44'])).
% 33.02/33.25  thf('46', plain,
% 33.02/33.25      (![X0 : $i]: ((v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X0 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['39', '40'])).
% 33.02/33.25  thf('47', plain,
% 33.02/33.25      (![X4 : $i, X7 : $i]:
% 33.02/33.25         (((X7) = (k1_zfmisc_1 @ X4))
% 33.02/33.25          | (r1_tarski @ (sk_C @ X7 @ X4) @ X4)
% 33.02/33.25          | (r2_hidden @ (sk_C @ X7 @ X4) @ X7))),
% 33.02/33.25      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 33.02/33.25  thf('48', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 33.02/33.25      inference('demod', [status(thm)], ['35', '36'])).
% 33.02/33.25  thf('49', plain,
% 33.02/33.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.02/33.25         (~ (r2_hidden @ X17 @ X18)
% 33.02/33.25          | ~ (v1_xboole_0 @ X19)
% 33.02/33.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 33.02/33.25      inference('cnf', [status(esa)], [t5_subset])).
% 33.02/33.25  thf('50', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['48', '49'])).
% 33.02/33.25  thf('51', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]:
% 33.02/33.25         ((r1_tarski @ (sk_C @ X0 @ X1) @ X1)
% 33.02/33.25          | ((X0) = (k1_zfmisc_1 @ X1))
% 33.02/33.25          | ~ (v1_xboole_0 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['47', '50'])).
% 33.02/33.25  thf('52', plain,
% 33.02/33.25      (![X3 : $i, X4 : $i, X5 : $i]:
% 33.02/33.25         (~ (r1_tarski @ X3 @ X4)
% 33.02/33.25          | (r2_hidden @ X3 @ X5)
% 33.02/33.25          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 33.02/33.25      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 33.02/33.25  thf('53', plain,
% 33.02/33.25      (![X3 : $i, X4 : $i]:
% 33.02/33.25         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 33.02/33.25      inference('simplify', [status(thm)], ['52'])).
% 33.02/33.25  thf('54', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]:
% 33.02/33.25         (~ (v1_xboole_0 @ X1)
% 33.02/33.25          | ((X1) = (k1_zfmisc_1 @ X0))
% 33.02/33.25          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 33.02/33.25      inference('sup-', [status(thm)], ['51', '53'])).
% 33.02/33.25  thf('55', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['48', '49'])).
% 33.02/33.25  thf('56', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]:
% 33.02/33.25         (((X1) = (k1_zfmisc_1 @ X0))
% 33.02/33.25          | ~ (v1_xboole_0 @ X1)
% 33.02/33.25          | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 33.02/33.25      inference('sup-', [status(thm)], ['54', '55'])).
% 33.02/33.25  thf('57', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]:
% 33.02/33.25         ((r1_tarski @ X0 @ X0)
% 33.02/33.25          | ~ (v1_xboole_0 @ X1)
% 33.02/33.25          | ((X1) = (k1_zfmisc_1 @ X0)))),
% 33.02/33.25      inference('sup-', [status(thm)], ['46', '56'])).
% 33.02/33.25  thf('58', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]:
% 33.02/33.25         ((r1_tarski @ X0 @ X0)
% 33.02/33.25          | ((X0) = (k1_zfmisc_1 @ X1))
% 33.02/33.25          | (r1_tarski @ X1 @ X1))),
% 33.02/33.25      inference('sup-', [status(thm)], ['45', '57'])).
% 33.02/33.25  thf('59', plain,
% 33.02/33.25      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | ((X0) = (k1_zfmisc_1 @ X0)))),
% 33.02/33.25      inference('eq_fact', [status(thm)], ['58'])).
% 33.02/33.25  thf('60', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 33.02/33.25      inference('demod', [status(thm)], ['35', '36'])).
% 33.02/33.25  thf('61', plain,
% 33.02/33.25      (![X0 : $i]: ((m1_subset_1 @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 33.02/33.25      inference('sup+', [status(thm)], ['59', '60'])).
% 33.02/33.25  thf('62', plain,
% 33.02/33.25      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | ((X0) = (k1_zfmisc_1 @ X0)))),
% 33.02/33.25      inference('eq_fact', [status(thm)], ['58'])).
% 33.02/33.25  thf('63', plain,
% 33.02/33.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 33.02/33.25         (~ (r2_hidden @ X17 @ X18)
% 33.02/33.25          | ~ (v1_xboole_0 @ X19)
% 33.02/33.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 33.02/33.25      inference('cnf', [status(esa)], [t5_subset])).
% 33.02/33.25  thf('64', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.02/33.25         (~ (m1_subset_1 @ X1 @ X0)
% 33.02/33.25          | (r1_tarski @ X0 @ X0)
% 33.02/33.25          | ~ (v1_xboole_0 @ X0)
% 33.02/33.25          | ~ (r2_hidden @ X2 @ X1))),
% 33.02/33.25      inference('sup-', [status(thm)], ['62', '63'])).
% 33.02/33.25  thf('65', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]:
% 33.02/33.25         ((r1_tarski @ X0 @ X0)
% 33.02/33.25          | ~ (r2_hidden @ X1 @ X0)
% 33.02/33.25          | ~ (v1_xboole_0 @ X0)
% 33.02/33.25          | (r1_tarski @ X0 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['61', '64'])).
% 33.02/33.25  thf('66', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]:
% 33.02/33.25         (~ (v1_xboole_0 @ X0)
% 33.02/33.25          | ~ (r2_hidden @ X1 @ X0)
% 33.02/33.25          | (r1_tarski @ X0 @ X0))),
% 33.02/33.25      inference('simplify', [status(thm)], ['65'])).
% 33.02/33.25  thf('67', plain, (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['41', '44'])).
% 33.02/33.25  thf('68', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 33.02/33.25      inference('clc', [status(thm)], ['66', '67'])).
% 33.02/33.25  thf('69', plain, ((r1_tarski @ sk_B @ sk_B)),
% 33.02/33.25      inference('sup-', [status(thm)], ['34', '68'])).
% 33.02/33.25  thf('70', plain,
% 33.02/33.25      (![X3 : $i, X4 : $i]:
% 33.02/33.25         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 33.02/33.25      inference('simplify', [status(thm)], ['52'])).
% 33.02/33.25  thf('71', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_B))),
% 33.02/33.25      inference('sup-', [status(thm)], ['69', '70'])).
% 33.02/33.25  thf('72', plain,
% 33.02/33.25      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 33.02/33.25      inference('sup-', [status(thm)], ['48', '49'])).
% 33.02/33.25  thf('73', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))),
% 33.02/33.25      inference('sup-', [status(thm)], ['71', '72'])).
% 33.02/33.25  thf('74', plain,
% 33.02/33.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.25        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 33.02/33.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 33.02/33.25      inference('clc', [status(thm)], ['33', '73'])).
% 33.02/33.25  thf('75', plain,
% 33.02/33.25      (![X24 : $i]:
% 33.02/33.25         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X24)
% 33.02/33.25            != (k1_tarski @ sk_C_2))
% 33.02/33.25          | ~ (v4_pre_topc @ X24 @ sk_A)
% 33.02/33.25          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 33.02/33.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.25  thf('76', plain,
% 33.02/33.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.25        | ~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 33.02/33.25        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 33.02/33.25            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 33.02/33.25            != (k1_tarski @ sk_C_2)))),
% 33.02/33.25      inference('sup-', [status(thm)], ['74', '75'])).
% 33.02/33.25  thf('77', plain,
% 33.02/33.25      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 33.02/33.25        | (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 33.02/33.25      inference('sup-', [status(thm)], ['8', '10'])).
% 33.02/33.25  thf('78', plain,
% 33.02/33.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.25        | (m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 33.02/33.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 33.02/33.25      inference('sup-', [status(thm)], ['14', '15'])).
% 33.02/33.25  thf('79', plain,
% 33.02/33.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.25  thf('80', plain,
% 33.02/33.25      (![X20 : $i, X21 : $i, X22 : $i]:
% 33.02/33.25         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 33.02/33.25          | ~ (v2_tex_2 @ X20 @ X21)
% 33.02/33.25          | (v4_pre_topc @ (sk_D @ X22 @ X20 @ X21) @ X21)
% 33.02/33.25          | ~ (r1_tarski @ X22 @ X20)
% 33.02/33.25          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 33.02/33.25          | ~ (l1_pre_topc @ X21))),
% 33.02/33.25      inference('cnf', [status(esa)], [d6_tex_2])).
% 33.02/33.25  thf('81', plain,
% 33.02/33.25      (![X0 : $i]:
% 33.02/33.25         (~ (l1_pre_topc @ sk_A)
% 33.02/33.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.25          | ~ (r1_tarski @ X0 @ sk_B)
% 33.02/33.25          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 33.02/33.25          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 33.02/33.25      inference('sup-', [status(thm)], ['79', '80'])).
% 33.02/33.25  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 33.02/33.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.25  thf('83', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 33.02/33.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.25  thf('84', plain,
% 33.02/33.25      (![X0 : $i]:
% 33.02/33.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 33.02/33.25          | ~ (r1_tarski @ X0 @ sk_B)
% 33.02/33.25          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 33.02/33.25      inference('demod', [status(thm)], ['81', '82', '83'])).
% 33.02/33.25  thf('85', plain,
% 33.02/33.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.25        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 33.02/33.25        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 33.02/33.25      inference('sup-', [status(thm)], ['78', '84'])).
% 33.02/33.25  thf('86', plain,
% 33.02/33.25      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 33.02/33.25        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 33.02/33.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.25      inference('sup-', [status(thm)], ['77', '85'])).
% 33.02/33.25  thf('87', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))),
% 33.02/33.25      inference('sup-', [status(thm)], ['71', '72'])).
% 33.02/33.25  thf('88', plain,
% 33.02/33.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 33.02/33.25        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A))),
% 33.02/33.25      inference('clc', [status(thm)], ['86', '87'])).
% 33.02/33.25  thf('89', plain,
% 33.02/33.25      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 33.02/33.25          (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_2))
% 33.02/33.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.25      inference('clc', [status(thm)], ['76', '88'])).
% 33.02/33.25  thf('90', plain,
% 33.02/33.25      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)
% 33.02/33.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.25      inference('clc', [status(thm)], ['23', '89'])).
% 33.02/33.25  thf('91', plain,
% 33.02/33.25      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 33.02/33.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 33.02/33.25      inference('sup-', [status(thm)], ['11', '90'])).
% 33.02/33.25  thf('92', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))),
% 33.02/33.25      inference('sup-', [status(thm)], ['71', '72'])).
% 33.02/33.25  thf('93', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 33.02/33.25      inference('clc', [status(thm)], ['91', '92'])).
% 33.02/33.25  thf('94', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 33.02/33.25      inference('demod', [status(thm)], ['3', '93'])).
% 33.02/33.25  thf('95', plain, ($false), inference('sup-', [status(thm)], ['0', '94'])).
% 33.02/33.25  
% 33.02/33.25  % SZS output end Refutation
% 33.02/33.25  
% 33.02/33.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
