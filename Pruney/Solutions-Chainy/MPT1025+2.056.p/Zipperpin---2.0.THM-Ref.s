%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hBXbueA5Hb

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 127 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  479 (1509 expanded)
%              Number of equality atoms :   15 (  47 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X24: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X24 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('19',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('22',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X10 @ X8 @ X9 ) @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('34',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X12 )
      | ( X13
        = ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['14','29','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hBXbueA5Hb
% 0.16/0.37  % Computer   : n022.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:46:26 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.45  % Solved by: fo/fo7.sh
% 0.23/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.45  % done 31 iterations in 0.012s
% 0.23/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.45  % SZS output start Refutation
% 0.23/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.45  thf(sk_E_type, type, sk_E: $i).
% 0.23/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.45  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.23/0.45  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.45  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.45  thf(t116_funct_2, conjecture,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.45       ( ![E:$i]:
% 0.23/0.45         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.23/0.45              ( ![F:$i]:
% 0.23/0.45                ( ( m1_subset_1 @ F @ A ) =>
% 0.23/0.45                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.23/0.45                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.45            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.45          ( ![E:$i]:
% 0.23/0.45            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.23/0.45                 ( ![F:$i]:
% 0.23/0.45                   ( ( m1_subset_1 @ F @ A ) =>
% 0.23/0.45                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.23/0.45                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.45    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.23/0.45  thf('0', plain,
% 0.23/0.45      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('1', plain,
% 0.23/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(redefinition_k7_relset_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.45       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.23/0.45  thf('2', plain,
% 0.23/0.45      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.45         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.23/0.45          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.23/0.45      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.23/0.45  thf('3', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.23/0.45           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.23/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.45  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.23/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.45  thf(t143_relat_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i]:
% 0.23/0.45     ( ( v1_relat_1 @ C ) =>
% 0.23/0.45       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.23/0.45         ( ?[D:$i]:
% 0.23/0.45           ( ( r2_hidden @ D @ B ) & 
% 0.23/0.45             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.23/0.45             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.23/0.45  thf('5', plain,
% 0.23/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.45         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.23/0.45          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ X8)
% 0.23/0.45          | ~ (v1_relat_1 @ X10))),
% 0.23/0.45      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.45  thf('6', plain,
% 0.23/0.45      ((~ (v1_relat_1 @ sk_D_1)
% 0.23/0.45        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.23/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.45  thf('7', plain,
% 0.23/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(cc2_relat_1, axiom,
% 0.23/0.45    (![A:$i]:
% 0.23/0.45     ( ( v1_relat_1 @ A ) =>
% 0.23/0.45       ( ![B:$i]:
% 0.23/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.45  thf('8', plain,
% 0.23/0.45      (![X3 : $i, X4 : $i]:
% 0.23/0.45         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.23/0.45          | (v1_relat_1 @ X3)
% 0.23/0.45          | ~ (v1_relat_1 @ X4))),
% 0.23/0.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.45  thf('9', plain,
% 0.23/0.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.23/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.45  thf(fc6_relat_1, axiom,
% 0.23/0.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.45  thf('10', plain,
% 0.23/0.45      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.23/0.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.45  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.23/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.45  thf('12', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.23/0.45      inference('demod', [status(thm)], ['6', '11'])).
% 0.23/0.45  thf('13', plain,
% 0.23/0.45      (![X24 : $i]:
% 0.23/0.45         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X24))
% 0.23/0.45          | ~ (r2_hidden @ X24 @ sk_C)
% 0.23/0.45          | ~ (m1_subset_1 @ X24 @ sk_A))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('14', plain,
% 0.23/0.45      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.23/0.45        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.45  thf('15', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.23/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.45  thf('16', plain,
% 0.23/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.45         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.23/0.45          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ (k1_relat_1 @ X10))
% 0.23/0.45          | ~ (v1_relat_1 @ X10))),
% 0.23/0.45      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.45  thf('17', plain,
% 0.23/0.45      ((~ (v1_relat_1 @ sk_D_1)
% 0.23/0.45        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.23/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.45  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 0.23/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.45  thf('19', plain,
% 0.23/0.45      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.23/0.45      inference('demod', [status(thm)], ['17', '18'])).
% 0.23/0.45  thf('20', plain,
% 0.23/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(dt_k1_relset_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i]:
% 0.23/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.45       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.45  thf('21', plain,
% 0.23/0.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.45         ((m1_subset_1 @ (k1_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 0.23/0.45          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.23/0.45      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.23/0.45  thf('22', plain,
% 0.23/0.45      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_D_1) @ 
% 0.23/0.45        (k1_zfmisc_1 @ sk_A))),
% 0.23/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.45  thf('23', plain,
% 0.23/0.45      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i]:
% 0.23/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.45  thf('24', plain,
% 0.23/0.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.45         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.23/0.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.23/0.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.45  thf('25', plain,
% 0.23/0.45      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.23/0.45      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.45  thf('26', plain,
% 0.23/0.45      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.45      inference('demod', [status(thm)], ['22', '25'])).
% 0.23/0.45  thf(t4_subset, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i]:
% 0.23/0.45     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.23/0.45       ( m1_subset_1 @ A @ C ) ))).
% 0.23/0.45  thf('27', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.23/0.45          | (m1_subset_1 @ X0 @ X2))),
% 0.23/0.45      inference('cnf', [status(esa)], [t4_subset])).
% 0.23/0.45  thf('28', plain,
% 0.23/0.45      (![X0 : $i]:
% 0.23/0.45         ((m1_subset_1 @ X0 @ sk_A)
% 0.23/0.45          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.23/0.45      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.45  thf('29', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)),
% 0.23/0.45      inference('sup-', [status(thm)], ['19', '28'])).
% 0.23/0.45  thf('30', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.23/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.45  thf('31', plain,
% 0.23/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.45         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.23/0.45          | (r2_hidden @ (k4_tarski @ (sk_D @ X10 @ X8 @ X9) @ X9) @ X10)
% 0.23/0.45          | ~ (v1_relat_1 @ X10))),
% 0.23/0.45      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.45  thf('32', plain,
% 0.23/0.45      ((~ (v1_relat_1 @ sk_D_1)
% 0.23/0.45        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.23/0.45           sk_D_1))),
% 0.23/0.45      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.45  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.23/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.45  thf('34', plain,
% 0.23/0.45      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.23/0.45      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.45  thf(t8_funct_1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i]:
% 0.23/0.45     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.45       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.23/0.45         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.23/0.45           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.23/0.45  thf('35', plain,
% 0.23/0.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.45         (~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ X12)
% 0.23/0.45          | ((X13) = (k1_funct_1 @ X12 @ X11))
% 0.23/0.45          | ~ (v1_funct_1 @ X12)
% 0.23/0.45          | ~ (v1_relat_1 @ X12))),
% 0.23/0.45      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.23/0.45  thf('36', plain,
% 0.23/0.45      ((~ (v1_relat_1 @ sk_D_1)
% 0.23/0.45        | ~ (v1_funct_1 @ sk_D_1)
% 0.23/0.45        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.23/0.45      inference('sup-', [status(thm)], ['34', '35'])).
% 0.23/0.45  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.23/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.45  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf('39', plain,
% 0.23/0.45      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.23/0.45      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.23/0.45  thf('40', plain, (((sk_E) != (sk_E))),
% 0.23/0.45      inference('demod', [status(thm)], ['14', '29', '39'])).
% 0.23/0.45  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.23/0.45  
% 0.23/0.45  % SZS output end Refutation
% 0.23/0.45  
% 0.23/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
