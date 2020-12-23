%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vFpvCcWns8

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 137 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  622 (1852 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_E @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_D_4 @ sk_E ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('33',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('36',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_4 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('43',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_4 @ sk_C_2 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_4 @ X26 ) @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['11','29','30','31','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vFpvCcWns8
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 76 iterations in 0.042s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(t47_relset_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.50                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.50                     ( ?[E:$i]:
% 0.21/0.50                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.50                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.50                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.21/0.50                        ( ?[E:$i]:
% 0.21/0.50                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.21/0.50                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)
% 0.21/0.50        | (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf(d4_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.21/0.50          | (r2_hidden @ X3 @ X6)
% 0.21/0.50          | ((X6) != (k1_relat_1 @ X5)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X26 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2)
% 0.21/0.50          | ~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 0.21/0.50         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.50         <= (~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 0.21/0.50       ~ ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf(d5_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.50          | (r2_hidden @ X11 @ X13)
% 0.21/0.50          | ((X13) != (k2_relat_1 @ X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         ((r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((r2_hidden @ sk_E @ (k2_relat_1 @ sk_C_2)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.21/0.50        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '21'])).
% 0.21/0.50  thf(t4_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.21/0.50          | (m1_subset_1 @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X0 @ sk_B)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_E @ sk_B))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((![X26 : $i]:
% 0.21/0.50          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2))))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2)) & 
% 0.21/0.50             (![X26 : $i]:
% 0.21/0.50                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (~
% 0.21/0.50       (![X26 : $i]:
% 0.21/0.50          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2))) | 
% 0.21/0.50       ~ ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 0.21/0.50       ((r2_hidden @ (k4_tarski @ sk_D_4 @ sk_E) @ sk_C_2))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((![X26 : $i]:
% 0.21/0.50          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2))) | 
% 0.21/0.50       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 0.21/0.50         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((r2_hidden @ sk_D_4 @ (k1_relat_1 @ sk_C_2)))
% 0.21/0.50         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X7 @ X6)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.21/0.50          | ((X6) != (k1_relat_1 @ X5)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X5 : $i, X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.21/0.50          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X5)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_D_4 @ (sk_D_1 @ sk_D_4 @ sk_C_2)) @ sk_C_2))
% 0.21/0.50         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         ((r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (((r2_hidden @ (sk_D_1 @ sk_D_4 @ sk_C_2) @ (k2_relat_1 @ sk_C_2)))
% 0.21/0.50         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X0 @ sk_B)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (((m1_subset_1 @ (sk_D_1 @ sk_D_4 @ sk_C_2) @ sk_B))
% 0.21/0.50         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_D_4 @ (sk_D_1 @ sk_D_4 @ sk_C_2)) @ sk_C_2))
% 0.21/0.50         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((![X26 : $i]:
% 0.21/0.50          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2)))
% 0.21/0.50         <= ((![X26 : $i]:
% 0.21/0.50                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2))))),
% 0.21/0.50      inference('split', [status(esa)], ['8'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_4 @ sk_C_2) @ sk_B))
% 0.21/0.50         <= (((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) & 
% 0.21/0.50             (![X26 : $i]:
% 0.21/0.50                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (~
% 0.21/0.50       (![X26 : $i]:
% 0.21/0.50          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.21/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_D_4 @ X26) @ sk_C_2))) | 
% 0.21/0.50       ~ ((r2_hidden @ sk_D_4 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.50  thf('46', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)],
% 0.21/0.50                ['11', '29', '30', '31', '45'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
