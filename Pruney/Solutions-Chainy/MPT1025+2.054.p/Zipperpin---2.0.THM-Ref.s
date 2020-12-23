%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZejGTNyG6B

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:50 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 127 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  454 (1456 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X29: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X29 ) )
      | ~ ( r2_hidden @ X29 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('19',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('26',plain,(
    ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('37',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['26','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZejGTNyG6B
% 0.13/0.36  % Computer   : n008.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:51:15 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 121 iterations in 0.100s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(t116_funct_2, conjecture,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57       ( ![E:$i]:
% 0.37/0.57         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.37/0.57              ( ![F:$i]:
% 0.37/0.57                ( ( m1_subset_1 @ F @ A ) =>
% 0.37/0.57                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.37/0.57                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57          ( ![E:$i]:
% 0.37/0.57            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.37/0.57                 ( ![F:$i]:
% 0.37/0.57                   ( ( m1_subset_1 @ F @ A ) =>
% 0.37/0.57                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.37/0.57                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.37/0.57          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.37/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.57  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.57  thf(t143_relat_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ C ) =>
% 0.37/0.57       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.37/0.57         ( ?[D:$i]:
% 0.37/0.57           ( ( r2_hidden @ D @ B ) & 
% 0.37/0.57             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.37/0.57             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.37/0.57          | (r2_hidden @ (sk_D @ X21 @ X19 @ X20) @ X19)
% 0.37/0.57          | ~ (v1_relat_1 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.57        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc2_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.37/0.57          | (v1_relat_1 @ X14)
% 0.37/0.57          | ~ (v1_relat_1 @ X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf(fc6_relat_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.57  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('12', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '11'])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X29 : $i]:
% 0.37/0.57         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X29))
% 0.37/0.57          | ~ (r2_hidden @ X29 @ sk_C_1)
% 0.37/0.57          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)
% 0.37/0.57        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.57  thf('15', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.37/0.57          | (r2_hidden @ (k4_tarski @ (sk_D @ X21 @ X19 @ X20) @ X20) @ X21)
% 0.37/0.57          | ~ (v1_relat_1 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.57        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.37/0.57           sk_D_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.37/0.57        sk_D_1)),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf(t8_funct_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.57           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.57         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.37/0.57          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 0.37/0.57          | ~ (v1_funct_1 @ X23)
% 0.37/0.57          | ~ (v1_relat_1 @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.57        | ~ (v1_funct_1 @ sk_D_1)
% 0.37/0.57        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.57  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('23', plain, ((v1_funct_1 @ sk_D_1)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))),
% 0.37/0.57      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)
% 0.37/0.57        | ((sk_E) != (sk_E)))),
% 0.37/0.57      inference('demod', [status(thm)], ['14', '24'])).
% 0.37/0.57  thf('26', plain, (~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.37/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.37/0.57        sk_D_1)),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t3_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.57  thf('30', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.57  thf(d3_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ X2)
% 0.37/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.37/0.57        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['27', '32'])).
% 0.37/0.57  thf(l54_zfmisc_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.37/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.57         ((r2_hidden @ X4 @ X5)
% 0.37/0.57          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.37/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.57  thf('35', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf(t1_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.57  thf('37', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.37/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain, ($false), inference('demod', [status(thm)], ['26', '37'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
