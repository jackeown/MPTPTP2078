%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.igUSwtLFTJ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:57 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 132 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  619 (1619 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X22 @ X20 ) @ X22 ) @ X20 )
      | ( X21
       != ( k2_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X22 @ X20 ) @ X22 ) @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('22',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B_1 )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) )
      & ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,
    ( ( r2_hidden @ sk_E @ sk_B_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) )
    | ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ( X21
       != ( k2_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k2_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['25','36','37','38','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.igUSwtLFTJ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 292 iterations in 0.320s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.77  thf(sk_E_type, type, sk_E: $i).
% 0.54/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.77  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.54/0.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.77  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.54/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.77  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.54/0.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.77  thf(t48_relset_1, conjecture,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.77       ( ![B:$i]:
% 0.54/0.77         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.77           ( ![C:$i]:
% 0.54/0.77             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.54/0.77               ( ![D:$i]:
% 0.54/0.77                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.54/0.77                   ( ?[E:$i]:
% 0.54/0.77                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.54/0.77                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.77    (~( ![A:$i]:
% 0.54/0.77        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.77          ( ![B:$i]:
% 0.54/0.77            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.77              ( ![C:$i]:
% 0.54/0.77                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.54/0.77                  ( ![D:$i]:
% 0.54/0.77                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.54/0.77                      ( ?[E:$i]:
% 0.54/0.77                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.54/0.77                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.54/0.77    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.54/0.77  thf('0', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.77  thf('1', plain,
% 0.54/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.77         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.54/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.54/0.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.77  thf('2', plain,
% 0.54/0.77      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.54/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.77  thf('3', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)
% 0.54/0.77        | (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('4', plain,
% 0.54/0.77      (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2)))
% 0.54/0.77         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('5', plain,
% 0.54/0.77      (((r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.54/0.77         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup+', [status(thm)], ['2', '4'])).
% 0.54/0.77  thf(d5_relat_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.54/0.77       ( ![C:$i]:
% 0.54/0.77         ( ( r2_hidden @ C @ B ) <=>
% 0.54/0.77           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.54/0.77  thf('6', plain,
% 0.54/0.77      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X22 @ X21)
% 0.54/0.77          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X22 @ X20) @ X22) @ X20)
% 0.54/0.77          | ((X21) != (k2_relat_1 @ X20)))),
% 0.54/0.77      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.54/0.77  thf('7', plain,
% 0.54/0.77      (![X20 : $i, X22 : $i]:
% 0.54/0.77         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X22 @ X20) @ X22) @ X20)
% 0.54/0.77          | ~ (r2_hidden @ X22 @ (k2_relat_1 @ X20)))),
% 0.54/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.54/0.77  thf('8', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.54/0.77         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['5', '7'])).
% 0.54/0.77  thf('9', plain,
% 0.54/0.77      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf(t3_subset, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.77  thf('10', plain,
% 0.54/0.77      (![X15 : $i, X16 : $i]:
% 0.54/0.77         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.77  thf('11', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.54/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.77  thf(d3_tarski, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.77  thf('12', plain,
% 0.54/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X3 @ X4)
% 0.54/0.77          | (r2_hidden @ X3 @ X5)
% 0.54/0.77          | ~ (r1_tarski @ X4 @ X5))),
% 0.54/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.77  thf('13', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))
% 0.54/0.77          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.54/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.77  thf('14', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ 
% 0.54/0.77         (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.54/0.77         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['8', '13'])).
% 0.54/0.77  thf(l54_zfmisc_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.77     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.54/0.77       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.54/0.77  thf('15', plain,
% 0.54/0.77      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.77         ((r2_hidden @ X7 @ X8)
% 0.54/0.77          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.54/0.77      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.54/0.77  thf('16', plain,
% 0.54/0.77      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B_1))
% 0.54/0.77         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.77  thf(d2_subset_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( ( v1_xboole_0 @ A ) =>
% 0.54/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.54/0.77       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.77  thf('17', plain,
% 0.54/0.77      (![X12 : $i, X13 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X12 @ X13)
% 0.54/0.77          | (m1_subset_1 @ X12 @ X13)
% 0.54/0.77          | (v1_xboole_0 @ X13))),
% 0.54/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.54/0.77  thf(d1_xboole_0, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.77  thf('18', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.77  thf('19', plain,
% 0.54/0.77      (![X12 : $i, X13 : $i]:
% 0.54/0.77         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.54/0.77      inference('clc', [status(thm)], ['17', '18'])).
% 0.54/0.77  thf('20', plain,
% 0.54/0.77      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B_1))
% 0.54/0.77         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['16', '19'])).
% 0.54/0.77  thf('21', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.54/0.77         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['5', '7'])).
% 0.54/0.77  thf('22', plain,
% 0.54/0.77      (![X28 : $i]:
% 0.54/0.77         (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77          | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2)
% 0.54/0.77          | ~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('23', plain,
% 0.54/0.77      ((![X28 : $i]:
% 0.54/0.77          (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2)))
% 0.54/0.77         <= ((![X28 : $i]:
% 0.54/0.77                (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2))))),
% 0.54/0.77      inference('split', [status(esa)], ['22'])).
% 0.54/0.77  thf('24', plain,
% 0.54/0.77      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B_1))
% 0.54/0.77         <= ((![X28 : $i]:
% 0.54/0.77                (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2))) & 
% 0.54/0.77             ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['21', '23'])).
% 0.54/0.77  thf('25', plain,
% 0.54/0.77      (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))) | 
% 0.54/0.77       ~
% 0.54/0.77       (![X28 : $i]:
% 0.54/0.77          (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['20', '24'])).
% 0.54/0.77  thf('26', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.54/0.77         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('27', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))
% 0.54/0.77          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.54/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.77  thf('28', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ 
% 0.54/0.77         (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.54/0.77         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.77  thf('29', plain,
% 0.54/0.77      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.77         ((r2_hidden @ X7 @ X8)
% 0.54/0.77          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.54/0.77      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.54/0.77  thf('30', plain,
% 0.54/0.77      (((r2_hidden @ sk_E @ sk_B_1))
% 0.54/0.77         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.77  thf('31', plain,
% 0.54/0.77      (![X12 : $i, X13 : $i]:
% 0.54/0.77         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.54/0.77      inference('clc', [status(thm)], ['17', '18'])).
% 0.54/0.77  thf('32', plain,
% 0.54/0.77      (((m1_subset_1 @ sk_E @ sk_B_1))
% 0.54/0.77         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.77  thf('33', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.54/0.77         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('34', plain,
% 0.54/0.77      ((![X28 : $i]:
% 0.54/0.77          (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2)))
% 0.54/0.77         <= ((![X28 : $i]:
% 0.54/0.77                (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2))))),
% 0.54/0.77      inference('split', [status(esa)], ['22'])).
% 0.54/0.77  thf('35', plain,
% 0.54/0.77      ((~ (m1_subset_1 @ sk_E @ sk_B_1))
% 0.54/0.77         <= ((![X28 : $i]:
% 0.54/0.77                (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2))) & 
% 0.54/0.77             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.77  thf('36', plain,
% 0.54/0.77      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.54/0.77       ~
% 0.54/0.77       (![X28 : $i]:
% 0.54/0.77          (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['32', '35'])).
% 0.54/0.77  thf('37', plain,
% 0.54/0.77      (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))) | 
% 0.54/0.77       (![X28 : $i]:
% 0.54/0.77          (~ (m1_subset_1 @ X28 @ sk_B_1)
% 0.54/0.77           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('split', [status(esa)], ['22'])).
% 0.54/0.77  thf('38', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.54/0.77       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2)))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('39', plain,
% 0.54/0.77      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.54/0.77         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('40', plain,
% 0.54/0.77      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.77         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.54/0.77          | (r2_hidden @ X19 @ X21)
% 0.54/0.77          | ((X21) != (k2_relat_1 @ X20)))),
% 0.54/0.77      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.54/0.77  thf('41', plain,
% 0.54/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.77         ((r2_hidden @ X19 @ (k2_relat_1 @ X20))
% 0.54/0.77          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.54/0.77      inference('simplify', [status(thm)], ['40'])).
% 0.54/0.77  thf('42', plain,
% 0.54/0.77      (((r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.54/0.77         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['39', '41'])).
% 0.54/0.77  thf('43', plain,
% 0.54/0.77      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.54/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.77  thf('44', plain,
% 0.54/0.77      ((~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2)))
% 0.54/0.77         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('split', [status(esa)], ['22'])).
% 0.54/0.77  thf('45', plain,
% 0.54/0.77      ((~ (r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.54/0.77         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['43', '44'])).
% 0.54/0.77  thf('46', plain,
% 0.54/0.77      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.54/0.77       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_2)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['42', '45'])).
% 0.54/0.77  thf('47', plain, ($false),
% 0.54/0.77      inference('sat_resolution*', [status(thm)],
% 0.54/0.77                ['25', '36', '37', '38', '46'])).
% 0.54/0.77  
% 0.54/0.77  % SZS output end Refutation
% 0.54/0.77  
% 0.54/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
