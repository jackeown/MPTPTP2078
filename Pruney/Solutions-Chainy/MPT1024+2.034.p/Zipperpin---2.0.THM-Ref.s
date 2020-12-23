%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T3pvTGB5Un

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 196 expanded)
%              Number of leaves         :   35 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  564 (2177 expanded)
%              Number of equality atoms :   13 (  58 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('27',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_A )
      | ~ ( r2_hidden @ X33 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('39',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ X24 )
      | ( X25
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,(
    v1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['25','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['14','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T3pvTGB5Un
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:45:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 88 iterations in 0.056s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(t115_funct_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ![E:$i]:
% 0.22/0.52         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.52              ( ![F:$i]:
% 0.22/0.52                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.52                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.52            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52          ( ![E:$i]:
% 0.22/0.52            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.52                 ( ![F:$i]:
% 0.22/0.52                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.52                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.22/0.52          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.22/0.52           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.52  thf(t143_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ C ) =>
% 0.22/0.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.52         ( ?[D:$i]:
% 0.22/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X22 @ X20 @ X21) @ (k1_relat_1 @ X22))
% 0.22/0.52          | ~ (v1_relat_1 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.52        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.52          | (v1_relat_1 @ X13)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf(fc6_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.52  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '11'])).
% 0.22/0.52  thf(d1_xboole_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('14', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.52         ((v4_relat_1 @ X26 @ X27)
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('17', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf(d18_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i]:
% 0.22/0.52         (~ (v4_relat_1 @ X15 @ X16)
% 0.22/0.52          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.22/0.52          | ~ (v1_relat_1 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf(t3_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X7 : $i, X9 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf(cc1_subset_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.52          | (v1_xboole_0 @ X3)
% 0.22/0.52          | ~ (v1_xboole_0 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '11'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf(t4_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X10 @ X11)
% 0.22/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.22/0.52          | (m1_subset_1 @ X10 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.52  thf(t2_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         ((r2_hidden @ X5 @ X6)
% 0.22/0.52          | (v1_xboole_0 @ X6)
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X33 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X33 @ sk_A)
% 0.22/0.52          | ~ (r2_hidden @ X33 @ sk_C)
% 0.22/0.52          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X33)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.22/0.52        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X22 @ X20 @ X21) @ X20)
% 0.22/0.52          | ~ (v1_relat_1 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.52        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('39', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '39'])).
% 0.22/0.52  thf('41', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ (sk_D @ X22 @ X20 @ X21) @ X21) @ X22)
% 0.22/0.52          | ~ (v1_relat_1 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.22/0.52           sk_D_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.52  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.52  thf(t8_funct_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ X24)
% 0.22/0.52          | ((X25) = (k1_funct_1 @ X24 @ X23))
% 0.22/0.52          | ~ (v1_funct_1 @ X24)
% 0.22/0.52          | ~ (v1_relat_1 @ X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.52        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('49', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.22/0.52      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.22/0.52  thf('51', plain, (((v1_xboole_0 @ sk_A) | ((sk_E) != (sk_E)))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '50'])).
% 0.22/0.52  thf('52', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.52  thf('53', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['25', '52'])).
% 0.22/0.52  thf('54', plain, ($false), inference('demod', [status(thm)], ['14', '53'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
