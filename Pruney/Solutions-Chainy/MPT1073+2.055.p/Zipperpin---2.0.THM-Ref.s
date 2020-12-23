%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.suPyQ7zono

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:21 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 118 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  490 (1322 expanded)
%              Number of equality atoms :   19 (  51 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k7_relset_1 @ X24 @ X25 @ X26 @ X24 )
        = ( k2_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X10 @ X8 @ X9 ) @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['10','15'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X12 )
      | ( X13
        = ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('20',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k9_relat_1 @ X10 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('26',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('29',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X27: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.suPyQ7zono
% 0.15/0.38  % Computer   : n020.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 12:32:22 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 32 iterations in 0.018s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.25/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.25/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.25/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.25/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.25/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.25/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.25/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.25/0.51  thf(t190_funct_2, conjecture,
% 0.25/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.25/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.25/0.51       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.25/0.51            ( ![E:$i]:
% 0.25/0.51              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.25/0.51            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.25/0.51          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.25/0.51               ( ![E:$i]:
% 0.25/0.51                 ( ( m1_subset_1 @ E @ B ) =>
% 0.25/0.51                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.25/0.51  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(t38_relset_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.51       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.25/0.51         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.25/0.51         (((k7_relset_1 @ X24 @ X25 @ X26 @ X24)
% 0.25/0.51            = (k2_relset_1 @ X24 @ X25 @ X26))
% 0.25/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.25/0.51      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      (((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ sk_B)
% 0.25/0.51         = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.25/0.51          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.25/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.25/0.51  thf('6', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.25/0.51           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.51  thf('7', plain,
% 0.25/0.51      (((k9_relat_1 @ sk_D_1 @ sk_B) = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.25/0.51      inference('demod', [status(thm)], ['3', '6'])).
% 0.25/0.51  thf('8', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.25/0.51      inference('demod', [status(thm)], ['0', '7'])).
% 0.25/0.51  thf(t143_relat_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ C ) =>
% 0.25/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.25/0.51         ( ?[D:$i]:
% 0.25/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.25/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.25/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.25/0.51  thf('9', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.25/0.51          | (r2_hidden @ (k4_tarski @ (sk_D @ X10 @ X8 @ X9) @ X9) @ X10)
% 0.25/0.51          | ~ (v1_relat_1 @ X10))),
% 0.25/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      ((~ (v1_relat_1 @ sk_D_1)
% 0.25/0.51        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.25/0.51           sk_D_1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.25/0.51  thf('11', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(cc2_relat_1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ A ) =>
% 0.25/0.51       ( ![B:$i]:
% 0.25/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.25/0.51          | (v1_relat_1 @ X3)
% 0.25/0.51          | ~ (v1_relat_1 @ X4))),
% 0.25/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.25/0.51  thf('13', plain,
% 0.25/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.25/0.51  thf(fc6_relat_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.25/0.51  thf('14', plain,
% 0.25/0.51      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.25/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.25/0.51  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.25/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.25/0.51  thf('16', plain,
% 0.25/0.51      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A) @ sk_D_1)),
% 0.25/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.25/0.51  thf(t8_funct_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.25/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.25/0.51           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.25/0.51  thf('17', plain,
% 0.25/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.25/0.51         (~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ X12)
% 0.25/0.51          | ((X13) = (k1_funct_1 @ X12 @ X11))
% 0.25/0.51          | ~ (v1_funct_1 @ X12)
% 0.25/0.51          | ~ (v1_relat_1 @ X12))),
% 0.25/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.25/0.51  thf('18', plain,
% 0.25/0.51      ((~ (v1_relat_1 @ sk_D_1)
% 0.25/0.51        | ~ (v1_funct_1 @ sk_D_1)
% 0.25/0.51        | ((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.25/0.51  thf('19', plain, ((v1_relat_1 @ sk_D_1)),
% 0.25/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.25/0.51  thf('20', plain, ((v1_funct_1 @ sk_D_1)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('21', plain,
% 0.25/0.51      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.25/0.51      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.25/0.51  thf('22', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.25/0.51      inference('demod', [status(thm)], ['0', '7'])).
% 0.25/0.51  thf('23', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X9 @ (k9_relat_1 @ X10 @ X8))
% 0.25/0.51          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ (k1_relat_1 @ X10))
% 0.25/0.51          | ~ (v1_relat_1 @ X10))),
% 0.25/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.25/0.51  thf('24', plain,
% 0.25/0.51      ((~ (v1_relat_1 @ sk_D_1)
% 0.25/0.51        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_D_1)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.25/0.51  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 0.25/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.25/0.51  thf('26', plain,
% 0.25/0.51      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_D_1))),
% 0.25/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.25/0.51  thf('27', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(dt_k1_relset_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.51       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.25/0.51  thf('28', plain,
% 0.25/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.51         ((m1_subset_1 @ (k1_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 0.25/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.25/0.51      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.25/0.51  thf('29', plain,
% 0.25/0.51      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_C @ sk_D_1) @ 
% 0.25/0.51        (k1_zfmisc_1 @ sk_B))),
% 0.25/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.25/0.51  thf('30', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.25/0.51  thf('31', plain,
% 0.25/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.25/0.51         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.25/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.25/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.25/0.51  thf('32', plain,
% 0.25/0.51      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.25/0.51  thf('33', plain,
% 0.25/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.25/0.51      inference('demod', [status(thm)], ['29', '32'])).
% 0.25/0.51  thf(t4_subset, axiom,
% 0.25/0.51    (![A:$i,B:$i,C:$i]:
% 0.25/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.25/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.25/0.51  thf('34', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.25/0.51          | (m1_subset_1 @ X0 @ X2))),
% 0.25/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.25/0.51  thf('35', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((m1_subset_1 @ X0 @ sk_B)
% 0.25/0.51          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.25/0.51  thf('36', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B)),
% 0.25/0.51      inference('sup-', [status(thm)], ['26', '35'])).
% 0.25/0.51  thf('37', plain,
% 0.25/0.51      (![X27 : $i]:
% 0.25/0.51         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X27))
% 0.25/0.51          | ~ (m1_subset_1 @ X27 @ sk_B))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('38', plain,
% 0.25/0.51      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.25/0.51  thf('39', plain, ($false),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['21', '38'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
