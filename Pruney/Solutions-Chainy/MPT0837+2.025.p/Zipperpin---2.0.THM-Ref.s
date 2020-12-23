%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HftZPYVRYj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:58 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 126 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  592 (1565 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X18 @ X16 ) @ X18 ) @ X16 )
      | ( X17
       != ( k2_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X18 @ X16 ) @ X18 ) @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('18',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('20',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_B )
   <= ( ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) )
      & ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
    | ~ ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ~ ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
    | ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X24 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k2_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k2_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_2 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['23','34','35','36','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HftZPYVRYj
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 171 iterations in 0.192s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.46/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.66  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.66  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(t48_relset_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.46/0.66               ( ![D:$i]:
% 0.46/0.66                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.46/0.66                   ( ?[E:$i]:
% 0.46/0.66                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.46/0.66                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.46/0.66                  ( ![D:$i]:
% 0.46/0.66                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.46/0.66                      ( ?[E:$i]:
% 0.46/0.66                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.46/0.66                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.46/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)
% 0.46/0.66        | (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))
% 0.46/0.66         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (((r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.46/0.66         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['2', '4'])).
% 0.46/0.66  thf(d5_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.66       ( ![C:$i]:
% 0.46/0.66         ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.66           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X18 @ X17)
% 0.46/0.66          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X18 @ X16) @ X18) @ X16)
% 0.46/0.66          | ((X17) != (k2_relat_1 @ X16)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X16 : $i, X18 : $i]:
% 0.46/0.66         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X18 @ X16) @ X18) @ X16)
% 0.46/0.66          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X16)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.46/0.66         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t3_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('11', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf(d3_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.66          | (r2_hidden @ X0 @ X2)
% 0.46/0.66          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.46/0.66          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ 
% 0.46/0.66         (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.46/0.66         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '13'])).
% 0.46/0.66  thf(l54_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.46/0.66       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         ((r2_hidden @ X4 @ X5)
% 0.46/0.66          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.46/0.66         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf(t1_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.46/0.66         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 0.46/0.66         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X24 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66          | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)
% 0.46/0.66          | ~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      ((![X24 : $i]:
% 0.46/0.66          (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66           | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)))
% 0.46/0.66         <= ((![X24 : $i]:
% 0.46/0.66                (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66                 | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2))))),
% 0.46/0.66      inference('split', [status(esa)], ['20'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_B))
% 0.46/0.66         <= ((![X24 : $i]:
% 0.46/0.66                (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66                 | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2))) & 
% 0.46/0.66             ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '21'])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))) | 
% 0.46/0.66       ~
% 0.46/0.66       (![X24 : $i]:
% 0.46/0.66          (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66           | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['18', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.46/0.66         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.46/0.66          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.46/0.66         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         ((r2_hidden @ X4 @ X5)
% 0.46/0.66          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (((r2_hidden @ sk_E @ sk_B))
% 0.46/0.66         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_E @ sk_B))
% 0.46/0.66         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.46/0.66         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((![X24 : $i]:
% 0.46/0.66          (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66           | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)))
% 0.46/0.66         <= ((![X24 : $i]:
% 0.46/0.66                (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66                 | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2))))),
% 0.46/0.66      inference('split', [status(esa)], ['20'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.46/0.66         <= ((![X24 : $i]:
% 0.46/0.66                (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66                 | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2))) & 
% 0.46/0.66             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.46/0.66       ~
% 0.46/0.66       (![X24 : $i]:
% 0.46/0.66          (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66           | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))) | 
% 0.46/0.66       (![X24 : $i]:
% 0.46/0.66          (~ (m1_subset_1 @ X24 @ sk_B)
% 0.46/0.66           | ~ (r2_hidden @ (k4_tarski @ X24 @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('split', [status(esa)], ['20'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.46/0.66       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2))
% 0.46/0.66         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16)
% 0.46/0.66          | (r2_hidden @ X15 @ X17)
% 0.46/0.66          | ((X17) != (k2_relat_1 @ X16)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.66         ((r2_hidden @ X15 @ (k2_relat_1 @ X16))
% 0.46/0.66          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.46/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (((r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.46/0.66         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['37', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      ((~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))
% 0.46/0.66         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('split', [status(esa)], ['20'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      ((~ (r2_hidden @ sk_D_2 @ (k2_relat_1 @ sk_C_2)))
% 0.46/0.66         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_2) @ sk_C_2)) | 
% 0.46/0.66       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '43'])).
% 0.46/0.66  thf('45', plain, ($false),
% 0.46/0.66      inference('sat_resolution*', [status(thm)],
% 0.46/0.66                ['23', '34', '35', '36', '44'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
