%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jvk9zwM3LD

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 164 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  538 (1371 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k5_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k7_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_C_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ sk_A @ sk_C_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['4','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jvk9zwM3LD
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:44:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 88 iterations in 0.032s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(t33_relset_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.19/0.46       ( m1_subset_1 @
% 0.19/0.46         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.19/0.46         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.19/0.46          ( m1_subset_1 @
% 0.19/0.46            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.19/0.46            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ sk_B) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(redefinition_k5_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.19/0.46          | ((k5_relset_1 @ X22 @ X23 @ X21 @ X24) = (k7_relat_1 @ X21 @ X24)))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((k5_relset_1 @ sk_A @ sk_C_1 @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.46  thf(d3_tarski, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X1 : $i, X3 : $i]:
% 0.19/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf(t88_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X13 : $i, X14 : $i]:
% 0.19/0.46         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.46          | (r2_hidden @ X0 @ X2)
% 0.19/0.46          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X0)
% 0.19/0.46          | (r2_hidden @ X2 @ X0)
% 0.19/0.46          | ~ (r2_hidden @ X2 @ (k7_relat_1 @ X0 @ X1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.46          | (r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ X1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '8'])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t3_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.46  thf('12', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.46          | (r2_hidden @ X0 @ X2)
% 0.19/0.46          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.19/0.46          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ sk_D)
% 0.19/0.46          | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.19/0.46          | (r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.19/0.46             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['9', '14'])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc2_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.19/0.46          | (v1_relat_1 @ X7)
% 0.19/0.46          | ~ (v1_relat_1 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)) | (v1_relat_1 @ sk_D))),
% 0.19/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.46  thf(fc6_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.46  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.46      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.19/0.46          | (r2_hidden @ (sk_C @ X1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.19/0.46             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('demod', [status(thm)], ['15', '20'])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X1 : $i, X3 : $i]:
% 0.19/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.19/0.46          | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.19/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (![X4 : $i, X6 : $i]:
% 0.19/0.46         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.46  thf(dt_k2_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.46         ((m1_subset_1 @ (k2_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.19/0.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ 
% 0.19/0.46          (k2_relset_1 @ sk_A @ sk_C_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.19/0.46          (k1_zfmisc_1 @ sk_C_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.46  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.46  thf('30', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.46         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.19/0.46          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((k2_relset_1 @ sk_A @ sk_C_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.19/0.46           = (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.19/0.46          (k1_zfmisc_1 @ sk_C_1))),
% 0.19/0.46      inference('demod', [status(thm)], ['28', '31'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.46  thf('34', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C_1)),
% 0.19/0.46      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.46  thf(t87_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i]:
% 0.19/0.46         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ X12)
% 0.19/0.46          | ~ (v1_relat_1 @ X11))),
% 0.19/0.46      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.19/0.46  thf(t11_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ C ) =>
% 0.19/0.46       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.19/0.46           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.19/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.19/0.46  thf('36', plain,
% 0.19/0.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.19/0.46          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 0.19/0.46          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.19/0.46          | ~ (v1_relat_1 @ X25))),
% 0.19/0.46      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.19/0.46  thf('37', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.46          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.19/0.46          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.19/0.46      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.46  thf('38', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C_1)))
% 0.19/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ sk_D))),
% 0.19/0.46      inference('sup-', [status(thm)], ['34', '37'])).
% 0.19/0.46  thf('39', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.46  thf('40', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.19/0.46          | (v1_relat_1 @ X7)
% 0.19/0.46          | ~ (v1_relat_1 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.46  thf('41', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.19/0.46          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.46  thf('42', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.46  thf('43', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.46  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.46      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('45', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C_1)))),
% 0.19/0.46      inference('demod', [status(thm)], ['38', '43', '44'])).
% 0.19/0.46  thf('46', plain, ($false), inference('demod', [status(thm)], ['4', '45'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
