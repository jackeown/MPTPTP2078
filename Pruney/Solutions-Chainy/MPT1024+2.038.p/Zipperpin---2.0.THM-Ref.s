%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T3VzQg4K3u

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 138 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  480 (1546 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X15 @ X13 @ X14 ) @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( X18
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_A )
      | ~ ( r2_hidden @ X26 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('41',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T3VzQg4K3u
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:31:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 37 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(t115_funct_2, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.47       ( ![E:$i]:
% 0.20/0.47         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.47              ( ![F:$i]:
% 0.20/0.47                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.47                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.47            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.47          ( ![E:$i]:
% 0.20/0.47            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.47                 ( ![F:$i]:
% 0.20/0.47                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.47                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.47          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.20/0.47           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.47  thf(t143_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.47         ( ?[D:$i]:
% 0.20/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.47             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.47             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ (sk_D @ X15 @ X13 @ X14) @ X14) @ X15)
% 0.20/0.47          | ~ (v1_relat_1 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.47        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.20/0.47           sk_D_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.47          | (v1_relat_1 @ X6)
% 0.20/0.47          | ~ (v1_relat_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf(fc6_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.47  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '11'])).
% 0.20/0.47  thf(t8_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.47         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.47           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.20/0.47          | ((X18) = (k1_funct_1 @ X17 @ X16))
% 0.20/0.47          | ~ (v1_funct_1 @ X17)
% 0.20/0.47          | ~ (v1_relat_1 @ X17))),
% 0.20/0.47      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.47        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('16', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.47  thf('18', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.20/0.47          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ (k1_relat_1 @ X15))
% 0.20/0.47          | ~ (v1_relat_1 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.47        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.47         ((v4_relat_1 @ X19 @ X20)
% 0.20/0.47          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.47  thf('25', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf(d18_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (v4_relat_1 @ X8 @ X9)
% 0.20/0.47          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.20/0.47          | ~ (v1_relat_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf(t3_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf(l3_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X26 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X26 @ sk_A)
% 0.20/0.47          | ~ (r2_hidden @ X26 @ sk_C)
% 0.20/0.47          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X26)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.20/0.47        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.20/0.47          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ X13)
% 0.20/0.47          | ~ (v1_relat_1 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.47        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('41', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.20/0.47      inference('demod', [status(thm)], ['36', '41'])).
% 0.20/0.47  thf('43', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['17', '42'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
