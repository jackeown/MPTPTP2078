%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gW3xJMVOTY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 113 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  513 (1172 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['9','12'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('20',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('33',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['26','37'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X27: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gW3xJMVOTY
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:26:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 52 iterations in 0.028s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(t190_funct_2, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.49       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.22/0.49            ( ![E:$i]:
% 0.22/0.49              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.49            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.49          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.22/0.49               ( ![E:$i]:
% 0.22/0.49                 ( ( m1_subset_1 @ E @ B ) =>
% 0.22/0.49                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.22/0.50  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.50         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.22/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf(t146_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X14 : $i]:
% 0.22/0.50         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 0.22/0.50          | ~ (v1_relat_1 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.22/0.50  thf(t143_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.50         ( ?[D:$i]:
% 0.22/0.50           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.50             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.50             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ X12) @ X13)
% 0.22/0.50          | ~ (v1_relat_1 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ 
% 0.22/0.50           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.50        | (r2_hidden @ 
% 0.22/0.50           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.22/0.50           sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( v1_relat_1 @ C ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.50         ((v1_relat_1 @ X18)
% 0.22/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.50  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((r2_hidden @ 
% 0.22/0.50        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.22/0.50        sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.50  thf(t8_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.50           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.22/0.50          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 0.22/0.50          | ~ (v1_funct_1 @ X16)
% 0.22/0.50          | ~ (v1_relat_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.50        | ((sk_A)
% 0.22/0.50            = (k1_funct_1 @ sk_D_1 @ 
% 0.22/0.50               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('17', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((sk_A)
% 0.22/0.50         = (k1_funct_1 @ sk_D_1 @ 
% 0.22/0.50            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.50  thf('19', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X14 : $i]:
% 0.22/0.50         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 0.22/0.50          | ~ (v1_relat_1 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.22/0.50          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ X11)
% 0.22/0.50          | ~ (v1_relat_1 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.22/0.50             (k1_relat_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.50        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.22/0.50           (k1_relat_1 @ sk_D_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '23'])).
% 0.22/0.50  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.22/0.50        (k1_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X21 @ X22)
% 0.22/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('29', plain, ((v4_relat_1 @ sk_D_1 @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf(d18_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (v4_relat_1 @ X8 @ X9)
% 0.22/0.50          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.22/0.50          | ~ (v1_relat_1 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('33', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X5 : $i, X7 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf(l3_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '37'])).
% 0.22/0.50  thf(t1_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      ((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X27 : $i]:
% 0.22/0.50         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X27))
% 0.22/0.50          | ~ (m1_subset_1 @ X27 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (((sk_A)
% 0.22/0.50         != (k1_funct_1 @ sk_D_1 @ 
% 0.22/0.50             (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['18', '42'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
