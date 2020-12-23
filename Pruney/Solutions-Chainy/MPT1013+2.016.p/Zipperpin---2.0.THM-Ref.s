%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H7clv4NB0e

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 (  94 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  594 (1411 expanded)
%              Number of equality atoms :   35 ( 102 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k9_relat_1 @ X4 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k9_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k9_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X7 @ X8 @ X10 @ X11 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18 )
        = ( k5_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k7_relset_1 @ X25 @ X26 @ X27 @ X25 )
        = ( k2_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('31',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_B @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_B @ X0 )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['28','36','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H7clv4NB0e
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:19:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 112 iterations in 0.096s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.54  thf(t73_funct_2, conjecture,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.54       ( ![C:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.54           ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.19/0.54               ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.19/0.54             ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.19/0.54               ( A ) ) ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i]:
% 0.19/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.54          ( ![C:$i]:
% 0.19/0.54            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.54              ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.19/0.54                  ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.19/0.54                ( ( k2_relset_1 @
% 0.19/0.54                    A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.19/0.54                  ( A ) ) ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t73_funct_2])).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.54         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.19/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.54  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.54  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('4', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.19/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.54  thf(t160_relat_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( v1_relat_1 @ B ) =>
% 0.19/0.54           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.54             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (![X4 : $i, X5 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X4)
% 0.19/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.19/0.54              = (k9_relat_1 @ X4 @ (k2_relat_1 @ X5)))
% 0.19/0.54          | ~ (v1_relat_1 @ X5))),
% 0.19/0.54      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ X0 @ sk_A))
% 0.19/0.54          | ~ (v1_relat_1 @ sk_C)
% 0.19/0.54          | ~ (v1_relat_1 @ X0))),
% 0.19/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(cc2_relat_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.19/0.54          | (v1_relat_1 @ X0)
% 0.19/0.54          | ~ (v1_relat_1 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.19/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.54  thf(fc6_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.54  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ X0 @ sk_A))
% 0.19/0.54          | ~ (v1_relat_1 @ X0))),
% 0.19/0.54      inference('demod', [status(thm)], ['6', '11'])).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.54         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(dt_k4_relset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.54     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.54       ( m1_subset_1 @
% 0.19/0.54         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.19/0.54         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.19/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.19/0.54          | (m1_subset_1 @ (k4_relset_1 @ X7 @ X8 @ X10 @ X11 @ X6 @ X9) @ 
% 0.19/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X11))))),
% 0.19/0.54      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.19/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      ((m1_subset_1 @ 
% 0.19/0.54        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 0.19/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.54         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.19/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.54         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.19/0.54         = (k2_relat_1 @ 
% 0.19/0.54            (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      (((k2_relat_1 @ (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.19/0.54         != (sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['13', '20'])).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(redefinition_k4_relset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.54     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.54       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.19/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.19/0.54          | ((k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18)
% 0.19/0.54              = (k5_relat_1 @ X15 @ X18)))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (((k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.19/0.54            = (k5_relat_1 @ sk_C @ X0))
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.19/0.54         = (k5_relat_1 @ sk_C @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['22', '25'])).
% 0.19/0.54  thf('27', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['21', '26'])).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      ((((k9_relat_1 @ sk_B @ sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['12', '27'])).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t38_relset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.54       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.54         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.54  thf('30', plain,
% 0.19/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.54         (((k7_relset_1 @ X25 @ X26 @ X27 @ X25)
% 0.19/0.54            = (k2_relset_1 @ X25 @ X26 @ X27))
% 0.19/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.19/0.54      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      (((k7_relset_1 @ sk_A @ sk_A @ sk_B @ sk_A)
% 0.19/0.54         = (k2_relset_1 @ sk_A @ sk_A @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.19/0.54          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((k7_relset_1 @ sk_A @ sk_A @ sk_B @ X0) = (k9_relat_1 @ sk_B @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.54  thf('35', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('36', plain, (((k9_relat_1 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['31', '34', '35'])).
% 0.19/0.54  thf('37', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('38', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.19/0.54          | (v1_relat_1 @ X0)
% 0.19/0.54          | ~ (v1_relat_1 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.54  thf('39', plain,
% 0.19/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.54  thf('40', plain,
% 0.19/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.54  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.54  thf('42', plain, (((sk_A) != (sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['28', '36', '41'])).
% 0.19/0.54  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
