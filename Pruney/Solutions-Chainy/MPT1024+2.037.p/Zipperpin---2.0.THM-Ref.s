%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.73k30GdtjX

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 136 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  462 (1528 expanded)
%              Number of equality atoms :   13 (  45 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_A )
      | ~ ( r2_hidden @ X24 @ sk_C_1 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('35',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ( X16
        = ( k1_funct_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('39',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['30','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.73k30GdtjX
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:15:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 48 iterations in 0.054s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(t115_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ![E:$i]:
% 0.21/0.52         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.21/0.52              ( ![F:$i]:
% 0.21/0.52                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.21/0.52                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52          ( ![E:$i]:
% 0.21/0.52            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.21/0.52                 ( ![F:$i]:
% 0.21/0.52                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.21/0.52                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.52          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.21/0.52           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.52  thf(t143_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.21/0.52         ( ?[D:$i]:
% 0.21/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.21/0.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.52        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.52          | (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf(fc6_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.52  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((v4_relat_1 @ X17 @ X18)
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('15', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf(d18_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (v4_relat_1 @ X6 @ X7)
% 0.21/0.52          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.21/0.52          | ~ (v1_relat_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf(d3_tarski, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.52          | (r2_hidden @ X0 @ X2)
% 0.21/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X24 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.52          | ~ (r2_hidden @ X24 @ sk_C_1)
% 0.21/0.52          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))
% 0.21/0.52        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ X11)
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.52        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('29', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '29'])).
% 0.21/0.52  thf('31', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ X12) @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.52        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.21/0.52           sk_D_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.21/0.52        sk_D_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf(t8_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.21/0.52          | ((X16) = (k1_funct_1 @ X15 @ X14))
% 0.21/0.52          | ~ (v1_funct_1 @ X15)
% 0.21/0.52          | ~ (v1_relat_1 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.52        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('39', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.52  thf('41', plain, (((sk_E) != (sk_E))),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '40'])).
% 0.21/0.52  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
