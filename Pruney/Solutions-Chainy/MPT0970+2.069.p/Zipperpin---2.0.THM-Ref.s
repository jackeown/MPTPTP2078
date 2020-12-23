%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d5LZPGm92H

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 289 expanded)
%              Number of leaves         :   31 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  601 (4262 expanded)
%              Number of equality atoms :   38 ( 292 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X17 @ X15 ) @ X15 )
      | ( ( k2_relset_1 @ X16 @ X15 @ X17 )
        = X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('9',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_D_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf('16',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X24 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X20 ) @ ( k2_relset_1 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf('27',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_B )
      | ( X24
        = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_D_1 @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( sk_D_1 @ sk_C @ sk_B ) ) @ ( sk_D_1 @ sk_C @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( sk_D_1 @ sk_C @ sk_B ) ) @ ( sk_D_1 @ sk_C @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X17 @ X15 ) ) @ X17 )
      | ( ( k2_relset_1 @ X16 @ X15 @ X17 )
        = X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','42'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','43'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('46',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['12','46','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d5LZPGm92H
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 40 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.21/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(t16_funct_2, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48       ( ( ![D:$i]:
% 0.21/0.48           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.48                ( ![E:$i]:
% 0.21/0.48                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.21/0.48                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.21/0.48         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48          ( ( ![D:$i]:
% 0.21/0.48              ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.48                   ( ![E:$i]:
% 0.21/0.48                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.21/0.48                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.21/0.48            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t23_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( ![D:$i]:
% 0.21/0.48           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.48                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.21/0.48         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_D_1 @ X17 @ X15) @ X15)
% 0.21/0.48          | ((k2_relset_1 @ X16 @ X15 @ X17) = (X15))
% 0.21/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.21/0.48      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.21/0.48        | (r2_hidden @ (sk_D_1 @ sk_C @ sk_B) @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.48  thf('5', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_C) = (sk_B))
% 0.21/0.48        | (r2_hidden @ (sk_D_1 @ sk_C @ sk_B) @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('9', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, ((r2_hidden @ (sk_D_1 @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('12', plain, (~ (r1_tarski @ sk_B @ (sk_D_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, ((r2_hidden @ (sk_D_1 @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X24 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X24 @ sk_B) | (r2_hidden @ (sk_E_1 @ X24) @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain, ((r2_hidden @ (sk_E_1 @ (sk_D_1 @ sk_C @ sk_B)) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t6_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X20 @ X21)
% 0.21/0.48          | ((X22) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_funct_1 @ X23)
% 0.21/0.48          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.21/0.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.48          | (r2_hidden @ (k1_funct_1 @ X23 @ X20) @ 
% 0.21/0.48             (k2_relset_1 @ X21 @ X22 @ X23)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.21/0.48           (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.48          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.48          | ((sk_B) = (k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.48          | ((sk_B) = (k1_xboole_0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((sk_B) = (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D_1 @ sk_C @ sk_B))) @ 
% 0.21/0.48           (k2_relat_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '24'])).
% 0.21/0.48  thf('26', plain, ((r2_hidden @ (sk_D_1 @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X24 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X24 @ sk_B)
% 0.21/0.48          | ((X24) = (k1_funct_1 @ sk_C @ (sk_E_1 @ X24))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((sk_D_1 @ sk_C @ sk_B)
% 0.21/0.48         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D_1 @ sk_C @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((sk_B) = (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ (sk_D_1 @ sk_C @ sk_B) @ (k2_relat_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '28'])).
% 0.21/0.48  thf(t146_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X9 : $i]:
% 0.21/0.48         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.21/0.48          | ~ (v1_relat_1 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.48  thf(t143_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.21/0.48         ( ?[D:$i]:
% 0.21/0.48           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.48             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.21/0.48             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ (sk_D @ X8 @ X6 @ X7) @ X7) @ X8)
% 0.21/0.48          | ~ (v1_relat_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ 
% 0.21/0.48           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (k4_tarski @ 
% 0.21/0.48            (sk_D @ sk_C @ (k1_relat_1 @ sk_C) @ (sk_D_1 @ sk_C @ sk_B)) @ 
% 0.21/0.48            (sk_D_1 @ sk_C @ sk_B)) @ 
% 0.21/0.48           sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc2_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.21/0.48          | (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf(fc6_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.48  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((((sk_B) = (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ 
% 0.21/0.48           (k4_tarski @ 
% 0.21/0.48            (sk_D @ sk_C @ (k1_relat_1 @ sk_C) @ (sk_D_1 @ sk_C @ sk_B)) @ 
% 0.21/0.48            (sk_D_1 @ sk_C @ sk_B)) @ 
% 0.21/0.48           sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X17 @ X15)) @ X17)
% 0.21/0.48          | ((k2_relset_1 @ X16 @ X15 @ X17) = (X15))
% 0.21/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.21/0.48      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_B) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.21/0.48          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_C) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['13', '43'])).
% 0.21/0.48  thf('45', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('46', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('49', plain, ($false),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '46', '47', '48'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
