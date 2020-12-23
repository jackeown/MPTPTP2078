%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1H4tjrRAF7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 146 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  619 (1808 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k7_relset_1 @ X24 @ X25 @ X26 @ X24 )
        = ( k2_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('10',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('15',plain,
    ( ( k9_relat_1 @ sk_C_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X16 @ X14 @ X15 ) @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('28',plain,
    ( ( k9_relat_1 @ sk_C_1 @ sk_B )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X14 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k2_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1H4tjrRAF7
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 95 iterations in 0.076s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(t48_relset_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.53                   ( ?[E:$i]:
% 0.20/0.53                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.53                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.53                  ( ![D:$i]:
% 0.20/0.53                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.53                      ( ?[E:$i]:
% 0.20/0.53                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.53                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X27 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1)
% 0.20/0.53          | ~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((![X27 : $i]:
% 0.20/0.53          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.53           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)
% 0.20/0.53        | (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.20/0.53         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.53         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t38_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.53         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (((k7_relset_1 @ X24 @ X25 @ X26 @ X24)
% 0.20/0.53            = (k2_relset_1 @ X24 @ X25 @ X26))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.53      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ sk_B)
% 0.20/0.53         = (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.53          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_relset_1 @ sk_B @ sk_A @ sk_C_1 @ X0)
% 0.20/0.53           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('15', plain, (((k9_relat_1 @ sk_C_1 @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.20/0.53  thf(t143_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.53         ( ?[D:$i]:
% 0.20/0.53           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.53             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.53             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X16 @ X14 @ X15) @ X15) @ X16)
% 0.20/0.53          | ~ (v1_relat_1 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.20/0.53             sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.53          | (v1_relat_1 @ X2)
% 0.20/0.53          | ~ (v1_relat_1 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.20/0.53             sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (((r2_hidden @ 
% 0.20/0.53         (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_D_3) @ sk_C_1))
% 0.20/0.53         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((![X27 : $i]:
% 0.20/0.53          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.53           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1)))
% 0.20/0.53         <= ((![X27 : $i]:
% 0.20/0.53                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.53                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.20/0.53         <= ((![X27 : $i]:
% 0.20/0.53                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.53                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) & 
% 0.20/0.53             ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.53         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.53  thf('28', plain, (((k9_relat_1 @ sk_C_1 @ sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.20/0.53          | (r2_hidden @ (sk_D_2 @ X16 @ X14 @ X15) @ X14)
% 0.20/0.53          | ~ (v1_relat_1 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.20/0.53         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '32'])).
% 0.20/0.53  thf(t1_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.20/0.53         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (~
% 0.20/0.53       (![X27 : $i]:
% 0.20/0.53          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.20/0.53           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.20/0.53       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf(d5_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.20/0.53          | (r2_hidden @ X5 @ X7)
% 0.20/0.53          | ((X7) != (k2_relat_1 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         ((r2_hidden @ X5 @ (k2_relat_1 @ X6))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.53         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.20/0.53       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.53  thf('46', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '45'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
