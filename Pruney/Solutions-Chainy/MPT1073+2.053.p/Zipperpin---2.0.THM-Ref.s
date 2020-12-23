%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VAY4NE1qi0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 316 expanded)
%              Number of leaves         :   29 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  636 (4097 expanded)
%              Number of equality atoms :   36 ( 183 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k7_relset_1 @ X21 @ X22 @ X23 @ X21 )
        = ( k2_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('3',plain,
    ( ( k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k7_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k9_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('21',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( X16
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ X0 ) @ sk_D_1 )
      | ( X0
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ X0 ) @ sk_D_1 )
      | ( X0
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['10','15'])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ( X15
       != ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ X14 @ X13 )
        = k1_xboole_0 )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( X16
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( X2
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('36',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('41',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('43',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X24: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ X0 ) @ sk_D_1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','46'])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','47'])).

thf('49',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['36','45'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VAY4NE1qi0
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 115 iterations in 0.064s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(t190_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.21/0.50            ( ![E:$i]:
% 0.21/0.50              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.50            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.21/0.50               ( ![E:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.50                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.21/0.50  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t38_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.50         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         (((k7_relset_1 @ X21 @ X22 @ X23 @ X21)
% 0.21/0.50            = (k2_relset_1 @ X21 @ X22 @ X23))
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ sk_B)
% 0.21/0.50         = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.50          | ((k7_relset_1 @ X18 @ X19 @ X17 @ X20) = (k9_relat_1 @ X17 @ X20)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.50           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((k9_relat_1 @ sk_D_1 @ sk_B) = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.50  thf('8', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf(t143_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.21/0.50         ( ?[D:$i]:
% 0.21/0.50           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.50             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.21/0.50             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.50        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.21/0.50           sk_D_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.21/0.50          | (v1_relat_1 @ X2)
% 0.21/0.50          | ~ (v1_relat_1 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf(fc6_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A) @ sk_D_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.50  thf('17', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.21/0.50          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.50        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_D_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf(d4_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ![B:$i,C:$i]:
% 0.21/0.50         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.50               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.50           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.50               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.21/0.50          | ((X16) = (k1_funct_1 @ X14 @ X13))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ X14)
% 0.21/0.50          | ~ (v1_funct_1 @ X14)
% 0.21/0.50          | ~ (v1_relat_1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ sk_D_1)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ X0) @ 
% 0.21/0.50               sk_D_1)
% 0.21/0.50          | ((X0) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('25', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ X0) @ 
% 0.21/0.50             sk_D_1)
% 0.21/0.50          | ((X0) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A) @ sk_D_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.21/0.50          | ((X15) = (k1_xboole_0))
% 0.21/0.50          | ((X15) != (k1_funct_1 @ X14 @ X13))
% 0.21/0.50          | ~ (v1_funct_1 @ X14)
% 0.21/0.50          | ~ (v1_relat_1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X14)
% 0.21/0.50          | ~ (v1_funct_1 @ X14)
% 0.21/0.50          | ((k1_funct_1 @ X14 @ X13) = (k1_xboole_0))
% 0.21/0.50          | (r2_hidden @ X13 @ (k1_relat_1 @ X14)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.21/0.50          | ((X16) = (k1_funct_1 @ X14 @ X13))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ X14)
% 0.21/0.50          | ~ (v1_funct_1 @ X14)
% 0.21/0.50          | ~ (v1_relat_1 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.21/0.50          | ((X2) = (k1_funct_1 @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((X2) = (k1_funct_1 @ X0 @ X1))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.21/0.50        | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_D_1)
% 0.21/0.50        | ((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '32'])).
% 0.21/0.50  thf('34', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.50  thf('37', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.21/0.50          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.50        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('41', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf(t1_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.50  thf('43', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X24 : $i]:
% 0.21/0.50         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X24))
% 0.21/0.50          | ~ (m1_subset_1 @ X24 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (((k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['36', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ X0) @ 
% 0.21/0.50             sk_D_1)
% 0.21/0.50          | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '46'])).
% 0.21/0.50  thf('48', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['36', '45'])).
% 0.21/0.50  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('52', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['48', '51'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
