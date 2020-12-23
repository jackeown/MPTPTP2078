%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vGvysXajHX

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:07 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 462 expanded)
%              Number of leaves         :   21 ( 143 expanded)
%              Depth                    :   28
%              Number of atoms          :  615 (4088 expanded)
%              Number of equality atoms :   20 ( 124 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t44_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

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

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( m1_subset_1 @ ( sk_B @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_C_3 )
      | ( r2_hidden @ X22 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_C_3 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_C_3 )
      | ( r2_hidden @ X22 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,
    ( ( r1_tarski @ sk_C_3 @ sk_B_1 )
    | ( r1_tarski @ sk_C_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ sk_C_3 @ sk_B_1 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('43',plain,(
    r2_hidden @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X13 @ X14 ) @ X14 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('47',plain,
    ( ( sk_B_1 = sk_C_3 )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B_1 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B_1 )
      | ( r2_hidden @ X22 @ sk_C_3 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_C_3 )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_C_3 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ sk_C_3 @ sk_B_1 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X13 @ X14 ) @ X13 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1 = sk_C_3 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1 = sk_C_3 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_B_1 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_xboole_0 @ sk_C_3 ),
    inference(demod,[status(thm)],['29','67'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B_1 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('73',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    k1_xboole_0 != sk_C_3 ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vGvysXajHX
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 367 iterations in 0.162s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.41/0.62  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(d1_xboole_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf(t44_setfam_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62           ( ( ![D:$i]:
% 0.41/0.62               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.62                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.41/0.62             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62          ( ![C:$i]:
% 0.41/0.62            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62              ( ( ![D:$i]:
% 0.41/0.62                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.62                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.41/0.62                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t2_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         ((r2_hidden @ X17 @ X18)
% 0.41/0.62          | (v1_xboole_0 @ X18)
% 0.41/0.62          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.41/0.62        | (r2_hidden @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.62  thf(d1_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.41/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.62          | (r1_tarski @ X11 @ X9)
% 0.41/0.62          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X9 : $i, X11 : $i]:
% 0.41/0.62         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.41/0.62        | (r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '6'])).
% 0.41/0.62  thf(d3_tarski, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X4 : $i, X6 : $i]:
% 0.41/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X4 : $i, X6 : $i]:
% 0.41/0.62         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.41/0.62      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X8 @ X9)
% 0.41/0.62          | (r2_hidden @ X8 @ X10)
% 0.41/0.62          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i]:
% 0.41/0.62         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.41/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.41/0.62  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf('16', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf('17', plain, ((r1_tarski @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['7', '16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X3 @ X4)
% 0.41/0.62          | (r2_hidden @ X3 @ X5)
% 0.41/0.62          | ~ (r1_tarski @ X4 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_C_3)
% 0.41/0.62        | (r2_hidden @ (sk_B @ sk_C_3) @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '19'])).
% 0.41/0.62  thf(t1_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_C_3)
% 0.41/0.62        | (m1_subset_1 @ (sk_B @ sk_C_3) @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X22 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X22 @ sk_C_3)
% 0.41/0.62          | (r2_hidden @ X22 @ sk_B_1)
% 0.41/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_C_3)
% 0.41/0.62        | (r2_hidden @ (sk_B @ sk_C_3) @ sk_B_1)
% 0.41/0.62        | ~ (r2_hidden @ (sk_B @ sk_C_3) @ sk_C_3))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      ((~ (r2_hidden @ (sk_B @ sk_C_3) @ sk_C_3)
% 0.41/0.62        | (r2_hidden @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.41/0.62      inference('clc', [status(thm)], ['24', '25'])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_C_3) | (r2_hidden @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['0', '26'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf('29', plain, (((v1_xboole_0 @ sk_C_3) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X4 : $i, X6 : $i]:
% 0.41/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r1_tarski @ sk_C_3 @ X0)
% 0.41/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r1_tarski @ sk_C_3 @ X0)
% 0.41/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_3) @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X22 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X22 @ sk_C_3)
% 0.41/0.62          | (r2_hidden @ X22 @ sk_B_1)
% 0.41/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r1_tarski @ sk_C_3 @ X0)
% 0.41/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_B_1)
% 0.41/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_C_3))),
% 0.41/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X4 : $i, X6 : $i]:
% 0.41/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_B_1)
% 0.41/0.62          | (r1_tarski @ sk_C_3 @ X0))),
% 0.41/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X4 : $i, X6 : $i]:
% 0.41/0.62         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      (((r1_tarski @ sk_C_3 @ sk_B_1) | (r1_tarski @ sk_C_3 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.62  thf('41', plain, ((r1_tarski @ sk_C_3 @ sk_B_1)),
% 0.41/0.62      inference('simplify', [status(thm)], ['40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i]:
% 0.41/0.62         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.41/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.41/0.62  thf('43', plain, ((r2_hidden @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.41/0.62  thf('45', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.62  thf(t49_subset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.62       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.41/0.62         ( ( A ) = ( B ) ) ) ))).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (sk_C_2 @ X13 @ X14) @ X14)
% 0.41/0.62          | ((X14) = (X13))
% 0.41/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      ((((sk_B_1) = (sk_C_3))
% 0.41/0.62        | (m1_subset_1 @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('48', plain, (((sk_B_1) != (sk_C_3))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('49', plain, ((m1_subset_1 @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_B_1)),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         ((r2_hidden @ X17 @ X18)
% 0.41/0.62          | (v1_xboole_0 @ X18)
% 0.41/0.62          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t4_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.62       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X19 @ X20)
% 0.41/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.41/0.62          | (m1_subset_1 @ X19 @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.62          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.62        | (m1_subset_1 @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      (![X22 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X22 @ sk_B_1)
% 0.41/0.62          | (r2_hidden @ X22 @ sk_C_3)
% 0.41/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_C_3)
% 0.41/0.62        | ~ (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.62  thf('60', plain,
% 0.41/0.62      ((~ (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_C_3))),
% 0.41/0.62      inference('clc', [status(thm)], ['58', '59'])).
% 0.41/0.62  thf('61', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.62        | (r2_hidden @ (sk_C_2 @ sk_C_3 @ sk_B_1) @ sk_C_3))),
% 0.41/0.62      inference('sup-', [status(thm)], ['51', '60'])).
% 0.41/0.62  thf('62', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i]:
% 0.41/0.62         (~ (r2_hidden @ (sk_C_2 @ X13 @ X14) @ X13)
% 0.41/0.62          | ((X14) = (X13))
% 0.41/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.41/0.62  thf('63', plain,
% 0.41/0.62      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.62        | ~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_1))
% 0.41/0.62        | ((sk_B_1) = (sk_C_3)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.41/0.62  thf('64', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.62  thf('65', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (sk_C_3)))),
% 0.41/0.62      inference('demod', [status(thm)], ['63', '64'])).
% 0.41/0.62  thf('66', plain, (((sk_B_1) != (sk_C_3))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('67', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.41/0.62  thf('68', plain, ((v1_xboole_0 @ sk_C_3)),
% 0.41/0.62      inference('demod', [status(thm)], ['29', '67'])).
% 0.41/0.62  thf(l13_xboole_0, axiom,
% 0.41/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.62  thf('69', plain,
% 0.41/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.62  thf('70', plain, (((sk_C_3) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.62  thf('71', plain, (((sk_B_1) != (sk_C_3))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('72', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.62  thf('74', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.62  thf('75', plain, (((k1_xboole_0) != (sk_C_3))),
% 0.41/0.62      inference('demod', [status(thm)], ['71', '74'])).
% 0.41/0.62  thf('76', plain, ($false),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['70', '75'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
