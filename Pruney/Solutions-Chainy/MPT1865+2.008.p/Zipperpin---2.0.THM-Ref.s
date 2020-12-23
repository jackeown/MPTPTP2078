%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p796fV0Y2W

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:21 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 322 expanded)
%              Number of leaves         :   24 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  651 (4067 expanded)
%              Number of equality atoms :   15 ( 109 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X34 @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( ( k6_domain_1 @ X41 @ X42 )
        = ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k6_domain_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('26',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X44 ) @ X43 @ ( sk_D @ X45 @ X43 @ X44 ) )
        = X45 )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('33',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ( m1_subset_1 @ ( sk_D @ X45 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('43',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X47: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X47 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X47 @ sk_A )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ( v4_pre_topc @ ( sk_D @ X45 @ X43 @ X44 ) @ X44 )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('55',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B_1 @ sk_A ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p796fV0Y2W
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 363 iterations in 0.292s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.73  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.54/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.73  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.54/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.73  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.54/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.54/0.73  thf(t33_tex_2, conjecture,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( l1_pre_topc @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.73           ( ( v2_tex_2 @ B @ A ) =>
% 0.54/0.73             ( ![C:$i]:
% 0.54/0.73               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.73                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.54/0.73                      ( ![D:$i]:
% 0.54/0.73                        ( ( m1_subset_1 @
% 0.54/0.73                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.73                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.54/0.73                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.54/0.73                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i]:
% 0.54/0.73        ( ( l1_pre_topc @ A ) =>
% 0.54/0.73          ( ![B:$i]:
% 0.54/0.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.73              ( ( v2_tex_2 @ B @ A ) =>
% 0.54/0.73                ( ![C:$i]:
% 0.54/0.73                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.73                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.54/0.73                         ( ![D:$i]:
% 0.54/0.73                           ( ( m1_subset_1 @
% 0.54/0.73                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.73                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.54/0.73                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.54/0.73                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t3_subset, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X36 : $i, X37 : $i]:
% 0.54/0.73         ((r1_tarski @ X36 @ X37) | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('2', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.73  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t1_subset, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X34 : $i, X35 : $i]:
% 0.54/0.73         ((m1_subset_1 @ X34 @ X35) | ~ (r2_hidden @ X34 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [t1_subset])).
% 0.54/0.73  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.73  thf(dt_k6_domain_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.54/0.73       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X39 : $i, X40 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ X39)
% 0.54/0.73          | ~ (m1_subset_1 @ X40 @ X39)
% 0.54/0.73          | (m1_subset_1 @ (k6_domain_1 @ X39 @ X40) @ (k1_zfmisc_1 @ X39)))),
% 0.54/0.73      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))
% 0.54/0.73        | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf('8', plain, ((m1_subset_1 @ sk_C_1 @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.73  thf(redefinition_k6_domain_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.54/0.73       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X41 : $i, X42 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ X41)
% 0.54/0.73          | ~ (m1_subset_1 @ X42 @ X41)
% 0.54/0.73          | ((k6_domain_1 @ X41 @ X42) = (k1_tarski @ X42)))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      ((((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.54/0.73        | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('11', plain, ((r2_hidden @ sk_C_1 @ sk_B_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(d1_xboole_0, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.73  thf('13', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.73  thf('14', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.54/0.73      inference('clc', [status(thm)], ['10', '13'])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))
% 0.54/0.73        | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['7', '14'])).
% 0.54/0.73  thf('16', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.54/0.73      inference('clc', [status(thm)], ['15', '16'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X36 : $i, X37 : $i]:
% 0.54/0.73         ((r1_tarski @ X36 @ X37) | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('19', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.73  thf(t1_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.54/0.73       ( r1_tarski @ A @ C ) ))).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.73         (~ (r1_tarski @ X3 @ X4)
% 0.54/0.73          | ~ (r1_tarski @ X4 @ X5)
% 0.54/0.73          | (r1_tarski @ X3 @ X5))),
% 0.54/0.73      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_tarski @ sk_C_1) @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.73  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['2', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X36 : $i, X38 : $i]:
% 0.54/0.73         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.54/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['22', '23'])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(d6_tex_2, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( l1_pre_topc @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.73           ( ( v2_tex_2 @ B @ A ) <=>
% 0.54/0.73             ( ![C:$i]:
% 0.54/0.73               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.73                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.54/0.73                      ( ![D:$i]:
% 0.54/0.73                        ( ( m1_subset_1 @
% 0.54/0.73                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.73                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.54/0.73                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.54/0.73                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.54/0.73          | ~ (v2_tex_2 @ X43 @ X44)
% 0.54/0.73          | ((k9_subset_1 @ (u1_struct_0 @ X44) @ X43 @ 
% 0.54/0.73              (sk_D @ X45 @ X43 @ X44)) = (X45))
% 0.54/0.73          | ~ (r1_tarski @ X45 @ X43)
% 0.54/0.73          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.54/0.73          | ~ (l1_pre_topc @ X44))),
% 0.54/0.73      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (l1_pre_topc @ sk_A)
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.54/0.73          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.54/0.73              (sk_D @ X0 @ sk_B_1 @ sk_A)) = (X0))
% 0.54/0.73          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.73  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('29', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.54/0.73          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.54/0.73              (sk_D @ X0 @ sk_B_1 @ sk_A)) = (X0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.54/0.73          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.54/0.73        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['24', '30'])).
% 0.54/0.73  thf('32', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.54/0.73         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['31', '32'])).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.54/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['22', '23'])).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.54/0.73          | ~ (v2_tex_2 @ X43 @ X44)
% 0.54/0.73          | (m1_subset_1 @ (sk_D @ X45 @ X43 @ X44) @ 
% 0.54/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.54/0.73          | ~ (r1_tarski @ X45 @ X43)
% 0.54/0.73          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.54/0.73          | ~ (l1_pre_topc @ X44))),
% 0.54/0.73      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (l1_pre_topc @ sk_A)
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.54/0.73          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ 
% 0.54/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.73  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('39', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('40', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.54/0.73          | (m1_subset_1 @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ 
% 0.54/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.73      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.54/0.73  thf('41', plain,
% 0.54/0.73      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A) @ 
% 0.54/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['34', '40'])).
% 0.54/0.73  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.73  thf('43', plain,
% 0.54/0.73      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A) @ 
% 0.54/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.54/0.73  thf('44', plain,
% 0.54/0.73      (![X47 : $i]:
% 0.54/0.73         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X47)
% 0.54/0.73            != (k1_tarski @ sk_C_1))
% 0.54/0.73          | ~ (v4_pre_topc @ X47 @ sk_A)
% 0.54/0.73          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('45', plain,
% 0.54/0.73      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A) @ sk_A)
% 0.54/0.73        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.54/0.73            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A))
% 0.54/0.73            != (k1_tarski @ sk_C_1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.54/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['22', '23'])).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('48', plain,
% 0.54/0.73      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.54/0.73          | ~ (v2_tex_2 @ X43 @ X44)
% 0.54/0.73          | (v4_pre_topc @ (sk_D @ X45 @ X43 @ X44) @ X44)
% 0.54/0.73          | ~ (r1_tarski @ X45 @ X43)
% 0.54/0.73          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.54/0.73          | ~ (l1_pre_topc @ X44))),
% 0.54/0.73      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.54/0.73  thf('49', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (l1_pre_topc @ sk_A)
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.54/0.73          | (v4_pre_topc @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ sk_A)
% 0.54/0.73          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.73  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('51', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('52', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.73          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.54/0.73          | (v4_pre_topc @ (sk_D @ X0 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.54/0.73      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.54/0.73  thf('53', plain,
% 0.54/0.73      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A) @ sk_A)
% 0.54/0.73        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['46', '52'])).
% 0.54/0.73  thf('54', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.73  thf('55', plain,
% 0.54/0.73      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A) @ sk_A)),
% 0.54/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.54/0.73  thf('56', plain,
% 0.54/0.73      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.54/0.73         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B_1 @ sk_A)) != (k1_tarski @ sk_C_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['45', '55'])).
% 0.54/0.73  thf('57', plain, ($false),
% 0.54/0.73      inference('simplify_reflect-', [status(thm)], ['33', '56'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
