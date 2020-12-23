%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zeSqyTIXze

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:36 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 242 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  595 (3137 expanded)
%              Number of equality atoms :    8 (  97 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t36_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v2_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v2_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v2_tops_2 @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                     => ( ( D = B )
                       => ( v2_tops_2 @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C_2 @ X14 @ X15 ) @ X15 )
      | ( v2_tops_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_C_3 )
    | ( v2_tops_2 @ sk_B @ sk_C_3 )
    | ~ ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C_3 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v2_tops_2 @ sk_B @ sk_C_3 )
    | ~ ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_C_3 ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ~ ( v2_tops_2 @ sk_D @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_D = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v2_tops_2 @ sk_B @ sk_C_3 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_C_3 ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X14 @ X15 ) @ X14 )
      | ( v2_tops_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_C_3 )
    | ( v2_tops_2 @ sk_B @ sk_C_3 )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_C_3 ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,
    ( ( v2_tops_2 @ sk_B @ sk_C_3 )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_tops_2 @ sk_B @ sk_C_3 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r1_tarski @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('41',plain,(
    r1_tarski @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( u1_struct_0 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t34_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ( X19 != X17 )
      | ~ ( m1_pre_topc @ X20 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_tops_2])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X20 @ X18 )
      | ( v4_pre_topc @ X17 @ X20 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ X0 )
      | ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_C_3 )
      | ~ ( m1_pre_topc @ sk_C_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_3 @ sk_A )
    | ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_C_3 )
    | ~ ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_C_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v2_tops_2 @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( v4_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_B )
    | ( v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_B ),
    inference(clc,[status(thm)],['19','20'])).

thf('59',plain,(
    v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_A ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v4_pre_topc @ ( sk_C_2 @ sk_B @ sk_C_3 ) @ sk_C_3 ),
    inference(demod,[status(thm)],['47','48','49','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['14','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zeSqyTIXze
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:39:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 159 iterations in 0.140s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(t36_tops_2, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @
% 0.41/0.60             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.60               ( ( v2_tops_2 @ B @ A ) =>
% 0.41/0.60                 ( ![D:$i]:
% 0.41/0.60                   ( ( m1_subset_1 @
% 0.41/0.60                       D @ 
% 0.41/0.60                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.41/0.60                     ( ( ( D ) = ( B ) ) => ( v2_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( l1_pre_topc @ A ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( m1_subset_1 @
% 0.41/0.60                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.60                  ( ( v2_tops_2 @ B @ A ) =>
% 0.41/0.60                    ( ![D:$i]:
% 0.41/0.60                      ( ( m1_subset_1 @
% 0.41/0.60                          D @ 
% 0.41/0.60                          ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.41/0.60                        ( ( ( D ) = ( B ) ) => ( v2_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t36_tops_2])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_D @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain, (((sk_D) = (sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3))))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf(d2_tops_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @
% 0.41/0.60             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.60           ( ( v2_tops_2 @ B @ A ) <=>
% 0.41/0.60             ( ![C:$i]:
% 0.41/0.60               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X14 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.41/0.60          | ~ (v4_pre_topc @ (sk_C_2 @ X14 @ X15) @ X15)
% 0.41/0.60          | (v2_tops_2 @ X14 @ X15)
% 0.41/0.60          | ~ (l1_pre_topc @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_C_3)
% 0.41/0.60        | (v2_tops_2 @ sk_B @ sk_C_3)
% 0.41/0.60        | ~ (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_C_3))),
% 0.41/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('5', plain, ((m1_pre_topc @ sk_C_3 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_m1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X12 @ X13)
% 0.41/0.60          | (l1_pre_topc @ X12)
% 0.41/0.60          | ~ (l1_pre_topc @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.60  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_3))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('9', plain, ((l1_pre_topc @ sk_C_3)),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (((v2_tops_2 @ sk_B @ sk_C_3)
% 0.41/0.60        | ~ (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_C_3))),
% 0.41/0.60      inference('demod', [status(thm)], ['4', '9'])).
% 0.41/0.60  thf('11', plain, (~ (v2_tops_2 @ sk_D @ sk_C_3)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('12', plain, (((sk_D) = (sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('13', plain, (~ (v2_tops_2 @ sk_B @ sk_C_3)),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain, (~ (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_C_3)),
% 0.41/0.60      inference('clc', [status(thm)], ['10', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3))))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X14 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.41/0.60          | (r2_hidden @ (sk_C_2 @ X14 @ X15) @ X14)
% 0.41/0.60          | (v2_tops_2 @ X14 @ X15)
% 0.41/0.60          | ~ (l1_pre_topc @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_C_3)
% 0.41/0.60        | (v2_tops_2 @ sk_B @ sk_C_3)
% 0.41/0.60        | (r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf('18', plain, ((l1_pre_topc @ sk_C_3)),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (((v2_tops_2 @ sk_B @ sk_C_3)
% 0.41/0.60        | (r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('20', plain, (~ (v2_tops_2 @ sk_B @ sk_C_3)),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('21', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_B)),
% 0.41/0.60      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t3_subset, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i]:
% 0.41/0.60         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('24', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.60  thf(d3_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.60          | (r2_hidden @ X0 @ X2)
% 0.41/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      ((r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '26'])).
% 0.41/0.60  thf(d1_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X7 @ X6)
% 0.41/0.60          | (r1_tarski @ X7 @ X5)
% 0.41/0.60          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X5 : $i, X7 : $i]:
% 0.41/0.60         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      ((r1_tarski @ (sk_C_2 @ sk_B @ sk_C_3) @ (u1_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['27', '29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X9 : $i, X11 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      ((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_C_3) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_B)),
% 0.41/0.60      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3))))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X9 : $i, X10 : $i]:
% 0.41/0.60         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.60          | (r2_hidden @ X0 @ X2)
% 0.41/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3)))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      ((r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '38'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X5 : $i, X7 : $i]:
% 0.41/0.60         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((r1_tarski @ (sk_C_2 @ sk_B @ sk_C_3) @ (u1_struct_0 @ sk_C_3))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X9 : $i, X11 : $i]:
% 0.41/0.60         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_C_3) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_3)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf(t34_tops_2, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.60               ( ( v4_pre_topc @ B @ A ) =>
% 0.41/0.60                 ( ![D:$i]:
% 0.41/0.60                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.41/0.60                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.60          | ~ (v4_pre_topc @ X17 @ X18)
% 0.41/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60          | (v4_pre_topc @ X19 @ X20)
% 0.41/0.60          | ((X19) != (X17))
% 0.41/0.60          | ~ (m1_pre_topc @ X20 @ X18)
% 0.41/0.60          | ~ (l1_pre_topc @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t34_tops_2])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X18)
% 0.41/0.60          | ~ (m1_pre_topc @ X20 @ X18)
% 0.41/0.60          | (v4_pre_topc @ X17 @ X20)
% 0.41/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.60          | ~ (v4_pre_topc @ X17 @ X18)
% 0.41/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_C_3) @ 
% 0.41/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ X0)
% 0.41/0.60          | (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_C_3)
% 0.41/0.60          | ~ (m1_pre_topc @ sk_C_3 @ X0)
% 0.41/0.60          | ~ (l1_pre_topc @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.60        | ~ (m1_pre_topc @ sk_C_3 @ sk_A)
% 0.41/0.60        | (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_C_3)
% 0.41/0.60        | ~ (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '46'])).
% 0.41/0.60  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('49', plain, ((m1_pre_topc @ sk_C_3 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      ((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_C_3) @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ 
% 0.41/0.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X14 @ 
% 0.41/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))
% 0.41/0.60          | ~ (v2_tops_2 @ X14 @ X15)
% 0.41/0.60          | ~ (r2_hidden @ X16 @ X14)
% 0.41/0.60          | (v4_pre_topc @ X16 @ X15)
% 0.41/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.41/0.60          | ~ (l1_pre_topc @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ sk_A)
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v4_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_B)
% 0.41/0.60          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.41/0.60  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('55', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.60          | (v4_pre_topc @ X0 @ sk_A)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      ((~ (r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_B)
% 0.41/0.60        | (v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['50', '56'])).
% 0.41/0.60  thf('58', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_B)),
% 0.41/0.60      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('59', plain, ((v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_A)),
% 0.41/0.60      inference('demod', [status(thm)], ['57', '58'])).
% 0.41/0.60  thf('60', plain, ((v4_pre_topc @ (sk_C_2 @ sk_B @ sk_C_3) @ sk_C_3)),
% 0.41/0.60      inference('demod', [status(thm)], ['47', '48', '49', '59'])).
% 0.41/0.60  thf('61', plain, ($false), inference('demod', [status(thm)], ['14', '60'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
