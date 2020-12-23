%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RuvPZXHKeg

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:23 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 319 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  688 (4936 expanded)
%              Number of equality atoms :   23 ( 162 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X3 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ ( sk_D @ X17 @ X15 @ X16 ) )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('33',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('39',plain,(
    ! [X19: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X19 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X19 @ sk_A )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v4_pre_topc @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('50',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('53',plain,(
    ( k3_xboole_0 @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RuvPZXHKeg
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:01:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 195 iterations in 0.124s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.58  thf(t33_tex_2, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_pre_topc @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( v2_tex_2 @ B @ A ) =>
% 0.40/0.58             ( ![C:$i]:
% 0.40/0.58               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.40/0.58                      ( ![D:$i]:
% 0.40/0.58                        ( ( m1_subset_1 @
% 0.40/0.58                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.40/0.58                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.40/0.58                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( l1_pre_topc @ A ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58              ( ( v2_tex_2 @ B @ A ) =>
% 0.40/0.58                ( ![C:$i]:
% 0.40/0.58                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.40/0.58                         ( ![D:$i]:
% 0.40/0.58                           ( ( m1_subset_1 @
% 0.40/0.58                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.40/0.58                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.40/0.58                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.40/0.58  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t38_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.40/0.58       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.40/0.58         ((r1_tarski @ (k2_tarski @ X3 @ X5) @ X6)
% 0.40/0.58          | ~ (r2_hidden @ X5 @ X6)
% 0.40/0.58          | ~ (r2_hidden @ X3 @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X0 @ sk_B)
% 0.40/0.58          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '3'])).
% 0.40/0.58  thf(t69_enumset1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.58  thf('5', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.58  thf(t28_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (k1_tarski @ sk_C_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(dt_k9_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.40/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.40/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k9_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.58         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.40/0.58           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.40/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['11', '14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['8', '15'])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d6_tex_2, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_pre_topc @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( v2_tex_2 @ B @ A ) <=>
% 0.40/0.58             ( ![C:$i]:
% 0.40/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.40/0.58                      ( ![D:$i]:
% 0.40/0.58                        ( ( m1_subset_1 @
% 0.40/0.58                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.40/0.58                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.40/0.58                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.58          | ~ (v2_tex_2 @ X15 @ X16)
% 0.40/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ 
% 0.40/0.58              (sk_D @ X17 @ X15 @ X16)) = (X17))
% 0.40/0.58          | ~ (r1_tarski @ X17 @ X15)
% 0.40/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.58          | ~ (l1_pre_topc @ X16))),
% 0.40/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.40/0.58          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.58              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.40/0.58          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.58  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('21', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.40/0.58          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.58              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.58          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.40/0.58        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['16', '22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['8', '15'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.58          | ~ (v2_tex_2 @ X15 @ X16)
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ X17 @ X15 @ X16) @ 
% 0.40/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.58          | ~ (r1_tarski @ X17 @ X15)
% 0.40/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.58          | ~ (l1_pre_topc @ X16))),
% 0.40/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.40/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('29', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.40/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.40/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['24', '30'])).
% 0.40/0.58  thf('32', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.58         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.40/0.58           (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.40/0.58           = (k3_xboole_0 @ X0 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.58  thf('36', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (((k3_xboole_0 @ sk_B @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.40/0.58         = (k1_tarski @ sk_C_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['23', '35', '36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X19 : $i]:
% 0.40/0.58         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X19)
% 0.40/0.58            != (k1_tarski @ sk_C_1))
% 0.40/0.58          | ~ (v4_pre_topc @ X19 @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.40/0.58        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.58            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.40/0.58            != (k1_tarski @ sk_C_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['8', '15'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.58          | ~ (v2_tex_2 @ X15 @ X16)
% 0.40/0.58          | (v4_pre_topc @ (sk_D @ X17 @ X15 @ X16) @ X16)
% 0.40/0.58          | ~ (r1_tarski @ X17 @ X15)
% 0.40/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.58          | ~ (l1_pre_topc @ X16))),
% 0.40/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.40/0.58          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.40/0.58          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.40/0.58  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('46', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.40/0.58          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.40/0.58        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['41', '47'])).
% 0.40/0.58  thf('49', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.40/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.58         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['40', '50'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.40/0.58           (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.40/0.58           = (k3_xboole_0 @ X0 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      (((k3_xboole_0 @ sk_B @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.40/0.58         != (k1_tarski @ sk_C_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.58  thf('54', plain, ($false),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['37', '53'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
