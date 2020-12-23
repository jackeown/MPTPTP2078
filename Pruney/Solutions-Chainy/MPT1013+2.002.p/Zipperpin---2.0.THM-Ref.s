%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SwXD5u8ul9

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:43 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 107 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  578 (1592 expanded)
%              Number of equality atoms :   37 ( 117 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t73_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ( ( ( k2_relset_1 @ A @ A @ B )
                = A )
              & ( ( k2_relset_1 @ A @ A @ C )
                = A ) )
           => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
              = A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
           => ( ( ( ( k2_relset_1 @ A @ A @ B )
                  = A )
                & ( ( k2_relset_1 @ A @ A @ C )
                  = A ) )
             => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
                = A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_2])).

thf('1',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k4_relset_1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v4_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('45',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['16','21','40','43','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SwXD5u8ul9
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 146 iterations in 0.114s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.58  thf(t160_relat_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( v1_relat_1 @ B ) =>
% 0.41/0.58           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.41/0.58             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]:
% 0.41/0.58         (~ (v1_relat_1 @ X2)
% 0.41/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.41/0.58              = (k9_relat_1 @ X2 @ (k2_relat_1 @ X3)))
% 0.41/0.58          | ~ (v1_relat_1 @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.41/0.58  thf(t73_funct_2, conjecture,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.41/0.58       ( ![C:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.41/0.58           ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.41/0.58               ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.41/0.58             ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.41/0.58               ( A ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i]:
% 0.41/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.41/0.58          ( ![C:$i]:
% 0.41/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.41/0.58              ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.41/0.58                  ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.41/0.58                ( ( k2_relset_1 @
% 0.41/0.58                    A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.41/0.58                  ( A ) ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t73_funct_2])).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.58         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(dt_k4_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.58     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.41/0.58       ( m1_subset_1 @
% 0.41/0.58         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.41/0.58         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.41/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.41/0.58          | (m1_subset_1 @ (k4_relset_1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15) @ 
% 0.41/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X17))))),
% 0.41/0.58      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.41/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.41/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      ((m1_subset_1 @ 
% 0.41/0.58        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['2', '5'])).
% 0.41/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.58         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.41/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.58         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.41/0.58         = (k2_relat_1 @ 
% 0.41/0.58            (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      (((k2_relat_1 @ (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.41/0.58         != (sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['1', '8'])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k4_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.58     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.41/0.58       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.41/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.41/0.58          | ((k4_relset_1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 0.41/0.58              = (k5_relat_1 @ X21 @ X24)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (((k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.41/0.58            = (k5_relat_1 @ sk_C @ X0))
% 0.41/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.41/0.58         = (k5_relat_1 @ sk_C @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['10', '13'])).
% 0.41/0.58  thf('15', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['9', '14'])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)) != (sk_A))
% 0.41/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['0', '15'])).
% 0.41/0.58  thf('17', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.58         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.41/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.58  thf('20', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('21', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.41/0.58      inference('sup+', [status(thm)], ['19', '20'])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc2_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.58         ((v4_relat_1 @ X9 @ X10)
% 0.41/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.58  thf('24', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.41/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.58  thf(t209_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.41/0.58       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (![X4 : $i, X5 : $i]:
% 0.41/0.58         (((X4) = (k7_relat_1 @ X4 @ X5))
% 0.41/0.58          | ~ (v4_relat_1 @ X4 @ X5)
% 0.41/0.58          | ~ (v1_relat_1 @ X4))),
% 0.41/0.58      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      ((~ (v1_relat_1 @ sk_B) | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc1_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( v1_relat_1 @ C ) ))).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.58         ((v1_relat_1 @ X6)
% 0.41/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.58  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.58  thf('30', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['26', '29'])).
% 0.41/0.58  thf(t148_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ B ) =>
% 0.41/0.58       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k9_relat_1 @ X0 @ X1))
% 0.41/0.58          | ~ (v1_relat_1 @ X0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.58  thf('32', plain,
% 0.41/0.58      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 0.41/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.41/0.58  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.58  thf('34', plain, (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.58         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.41/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.58  thf('38', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('39', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.41/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.41/0.58  thf('40', plain, (((sk_A) = (k9_relat_1 @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['34', '39'])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('42', plain,
% 0.41/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.58         ((v1_relat_1 @ X6)
% 0.41/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.58  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.58  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.58  thf('45', plain, (((sk_A) != (sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['16', '21', '40', '43', '44'])).
% 0.41/0.58  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
