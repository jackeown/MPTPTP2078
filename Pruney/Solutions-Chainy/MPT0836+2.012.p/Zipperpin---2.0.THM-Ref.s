%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6k0vBQehMi

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:53 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 127 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  621 (1778 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t47_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                    <=> ? [E: $i] :
                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                          & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('2',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_D_1 @ X15 @ X13 ) ) @ X13 )
      | ( X14
       != ( k1_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_D_1 @ X15 @ X13 ) ) @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('20',plain,(
    ! [X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ! [X21: $i] :
        ( ~ ( m1_subset_1 @ X21 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) )
   <= ! [X21: $i] :
        ( ~ ( m1_subset_1 @ X21 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X21: $i] :
          ( ~ ( m1_subset_1 @ X21 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ! [X21: $i] :
          ( ~ ( m1_subset_1 @ X21 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( m1_subset_1 @ sk_E @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,
    ( ! [X21: $i] :
        ( ~ ( m1_subset_1 @ X21 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) )
   <= ! [X21: $i] :
        ( ~ ( m1_subset_1 @ X21 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
      & ! [X21: $i] :
          ( ~ ( m1_subset_1 @ X21 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ~ ! [X21: $i] :
          ( ~ ( m1_subset_1 @ X21 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ! [X21: $i] :
        ( ~ ( m1_subset_1 @ X21 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X11 @ X14 )
      | ( X14
       != ( k1_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['23','36','37','38','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6k0vBQehMi
% 0.12/0.36  % Computer   : n006.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 17:18:53 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 176 iterations in 0.135s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.60  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.41/0.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.41/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(t47_relset_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( m1_subset_1 @ D @ A ) =>
% 0.41/0.60                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.41/0.60                     ( ?[E:$i]:
% 0.41/0.60                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.41/0.60                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60                  ( ![D:$i]:
% 0.41/0.60                    ( ( m1_subset_1 @ D @ A ) =>
% 0.41/0.60                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.41/0.60                        ( ?[E:$i]:
% 0.41/0.60                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.41/0.60                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.60         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.41/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)
% 0.41/0.60        | (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '4'])).
% 0.41/0.60  thf(d4_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.41/0.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X15 @ X14)
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ X15 @ (sk_D_1 @ X15 @ X13)) @ X13)
% 0.41/0.60          | ((X14) != (k1_relat_1 @ X13)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X13 : $i, X15 : $i]:
% 0.41/0.60         ((r2_hidden @ (k4_tarski @ X15 @ (sk_D_1 @ X15 @ X13)) @ X13)
% 0.41/0.60          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X13)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(l3_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X8 @ X9)
% 0.41/0.60          | (r2_hidden @ X8 @ X10)
% 0.41/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.41/0.60      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ 
% 0.41/0.60         (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['8', '11'])).
% 0.41/0.60  thf(l54_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.41/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ X3)
% 0.41/0.60          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf(d2_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.60         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.60       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.60         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X5 @ X6)
% 0.41/0.60          | (m1_subset_1 @ X5 @ X6)
% 0.41/0.60          | (v1_xboole_0 @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      ((((v1_xboole_0 @ sk_B)
% 0.41/0.60         | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B)))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.60  thf('17', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('clc', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X21 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1)
% 0.41/0.60          | ~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((![X21 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1)))
% 0.41/0.60         <= ((![X21 : $i]:
% 0.41/0.60                (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1))))),
% 0.41/0.60      inference('split', [status(esa)], ['20'])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.41/0.60         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.41/0.60             (![X21 : $i]:
% 0.41/0.60                (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '21'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.41/0.60       ~
% 0.41/0.60       (![X21 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ X3)
% 0.41/0.60          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (((r2_hidden @ sk_E @ sk_B))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X5 @ X6)
% 0.41/0.60          | (m1_subset_1 @ X5 @ X6)
% 0.41/0.60          | (v1_xboole_0 @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      ((((v1_xboole_0 @ sk_B) | (m1_subset_1 @ sk_E @ sk_B)))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (((m1_subset_1 @ sk_E @ sk_B))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      ((![X21 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1)))
% 0.41/0.60         <= ((![X21 : $i]:
% 0.41/0.60                (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1))))),
% 0.41/0.60      inference('split', [status(esa)], ['20'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) & 
% 0.41/0.60             (![X21 : $i]:
% 0.41/0.60                (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 0.41/0.60       ~
% 0.41/0.60       (![X21 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.41/0.60       (![X21 : $i]:
% 0.41/0.60          (~ (m1_subset_1 @ X21 @ sk_B)
% 0.41/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['20'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 0.41/0.60       ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.60         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 0.41/0.60          | (r2_hidden @ X11 @ X14)
% 0.41/0.60          | ((X14) != (k1_relat_1 @ X13)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.60         ((r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.41/0.60          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 0.41/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.41/0.60         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '41'])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.41/0.60         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('split', [status(esa)], ['20'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.41/0.60         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 0.41/0.60       ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['42', '45'])).
% 0.41/0.60  thf('47', plain, ($false),
% 0.41/0.60      inference('sat_resolution*', [status(thm)],
% 0.41/0.60                ['23', '36', '37', '38', '46'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
