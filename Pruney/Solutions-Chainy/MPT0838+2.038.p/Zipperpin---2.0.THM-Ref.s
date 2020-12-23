%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WZ8RQLjdoo

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:03 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   78 (  96 expanded)
%              Number of leaves         :   34 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  476 ( 812 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('1',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X30 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X30 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['10','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X30: $i] :
      ~ ( r2_hidden @ X30 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['5','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','21'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('23',plain,(
    ! [X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WZ8RQLjdoo
% 0.06/0.27  % Computer   : n015.cluster.edu
% 0.06/0.27  % Model      : x86_64 x86_64
% 0.06/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.27  % Memory     : 8042.1875MB
% 0.06/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.27  % CPULimit   : 60
% 0.06/0.27  % DateTime   : Tue Dec  1 10:00:23 EST 2020
% 0.06/0.28  % CPUTime    : 
% 0.06/0.28  % Running portfolio for 600 s
% 0.06/0.28  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.06/0.28  % Number of cores: 8
% 0.06/0.28  % Python version: Python 3.6.8
% 0.06/0.28  % Running in FO mode
% 0.13/0.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.13/0.40  % Solved by: fo/fo7.sh
% 0.13/0.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.13/0.40  % done 64 iterations in 0.032s
% 0.13/0.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.13/0.40  % SZS output start Refutation
% 0.13/0.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.13/0.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.13/0.40  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.13/0.40  thf(sk_C_type, type, sk_C: $i).
% 0.13/0.40  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.13/0.40  thf(sk_B_type, type, sk_B: $i > $i).
% 0.13/0.40  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.13/0.40  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.13/0.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.13/0.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.13/0.40  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.13/0.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.13/0.40  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.13/0.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.13/0.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.13/0.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.13/0.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.13/0.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.13/0.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.13/0.40  thf(sk_A_type, type, sk_A: $i).
% 0.13/0.40  thf(t7_xboole_0, axiom,
% 0.13/0.40    (![A:$i]:
% 0.13/0.40     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.13/0.40          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.13/0.40  thf('0', plain,
% 0.13/0.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.13/0.40      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.13/0.40  thf(t49_relset_1, conjecture,
% 0.13/0.40    (![A:$i]:
% 0.13/0.40     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.13/0.40       ( ![B:$i]:
% 0.13/0.40         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.13/0.40           ( ![C:$i]:
% 0.13/0.40             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.13/0.40                    ( ![D:$i]:
% 0.13/0.40                      ( ( m1_subset_1 @ D @ B ) =>
% 0.13/0.40                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.13/0.40  thf(zf_stmt_0, negated_conjecture,
% 0.13/0.40    (~( ![A:$i]:
% 0.13/0.40        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.13/0.40          ( ![B:$i]:
% 0.13/0.40            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.13/0.40              ( ![C:$i]:
% 0.13/0.40                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.13/0.40                       ( ![D:$i]:
% 0.13/0.40                         ( ( m1_subset_1 @ D @ B ) =>
% 0.13/0.40                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.13/0.40    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.13/0.40  thf('1', plain,
% 0.13/0.40      (![X30 : $i]:
% 0.13/0.40         (~ (r2_hidden @ X30 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.13/0.40          | ~ (m1_subset_1 @ X30 @ sk_B_1))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf('2', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(redefinition_k2_relset_1, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.13/0.40  thf('3', plain,
% 0.13/0.40      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.13/0.40         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.13/0.40          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.13/0.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.13/0.40  thf('4', plain,
% 0.13/0.40      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.13/0.40      inference('sup-', [status(thm)], ['2', '3'])).
% 0.13/0.40  thf('5', plain,
% 0.13/0.40      (![X30 : $i]:
% 0.13/0.40         (~ (r2_hidden @ X30 @ (k2_relat_1 @ sk_C))
% 0.13/0.40          | ~ (m1_subset_1 @ X30 @ sk_B_1))),
% 0.13/0.40      inference('demod', [status(thm)], ['1', '4'])).
% 0.13/0.40  thf('6', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(cc2_relset_1, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.13/0.40  thf('7', plain,
% 0.13/0.40      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.13/0.40         ((v5_relat_1 @ X21 @ X23)
% 0.13/0.40          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.13/0.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.13/0.40  thf('8', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.13/0.40      inference('sup-', [status(thm)], ['6', '7'])).
% 0.13/0.40  thf(d19_relat_1, axiom,
% 0.13/0.40    (![A:$i,B:$i]:
% 0.13/0.40     ( ( v1_relat_1 @ B ) =>
% 0.13/0.40       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.13/0.40  thf('9', plain,
% 0.13/0.40      (![X12 : $i, X13 : $i]:
% 0.13/0.40         (~ (v5_relat_1 @ X12 @ X13)
% 0.13/0.40          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.13/0.40          | ~ (v1_relat_1 @ X12))),
% 0.13/0.40      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.13/0.40  thf('10', plain,
% 0.13/0.40      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.13/0.40      inference('sup-', [status(thm)], ['8', '9'])).
% 0.13/0.40  thf('11', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(cc2_relat_1, axiom,
% 0.13/0.40    (![A:$i]:
% 0.13/0.40     ( ( v1_relat_1 @ A ) =>
% 0.13/0.40       ( ![B:$i]:
% 0.13/0.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.13/0.40  thf('12', plain,
% 0.13/0.40      (![X10 : $i, X11 : $i]:
% 0.13/0.40         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.13/0.40          | (v1_relat_1 @ X10)
% 0.13/0.40          | ~ (v1_relat_1 @ X11))),
% 0.13/0.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.13/0.40  thf('13', plain,
% 0.13/0.40      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 0.13/0.40      inference('sup-', [status(thm)], ['11', '12'])).
% 0.13/0.40  thf(fc6_relat_1, axiom,
% 0.13/0.40    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.13/0.40  thf('14', plain,
% 0.13/0.40      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.13/0.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.13/0.40  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.13/0.40      inference('demod', [status(thm)], ['13', '14'])).
% 0.13/0.40  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.13/0.40      inference('demod', [status(thm)], ['10', '15'])).
% 0.13/0.40  thf(t3_subset, axiom,
% 0.13/0.40    (![A:$i,B:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.13/0.40  thf('17', plain,
% 0.13/0.40      (![X4 : $i, X6 : $i]:
% 0.13/0.40         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.13/0.40      inference('cnf', [status(esa)], [t3_subset])).
% 0.13/0.40  thf('18', plain,
% 0.13/0.40      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.13/0.40      inference('sup-', [status(thm)], ['16', '17'])).
% 0.13/0.40  thf(t4_subset, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i]:
% 0.13/0.40     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.13/0.40       ( m1_subset_1 @ A @ C ) ))).
% 0.13/0.40  thf('19', plain,
% 0.13/0.40      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.13/0.40         (~ (r2_hidden @ X7 @ X8)
% 0.13/0.40          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.13/0.40          | (m1_subset_1 @ X7 @ X9))),
% 0.13/0.40      inference('cnf', [status(esa)], [t4_subset])).
% 0.13/0.40  thf('20', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.13/0.40          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.13/0.40      inference('sup-', [status(thm)], ['18', '19'])).
% 0.13/0.40  thf('21', plain, (![X30 : $i]: ~ (r2_hidden @ X30 @ (k2_relat_1 @ sk_C))),
% 0.13/0.40      inference('clc', [status(thm)], ['5', '20'])).
% 0.13/0.40  thf('22', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.13/0.40      inference('sup-', [status(thm)], ['0', '21'])).
% 0.13/0.40  thf(t98_relat_1, axiom,
% 0.13/0.40    (![A:$i]:
% 0.13/0.40     ( ( v1_relat_1 @ A ) =>
% 0.13/0.40       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.13/0.40  thf('23', plain,
% 0.13/0.40      (![X20 : $i]:
% 0.13/0.40         (((k7_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (X20))
% 0.13/0.40          | ~ (v1_relat_1 @ X20))),
% 0.13/0.40      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.13/0.40  thf(t148_relat_1, axiom,
% 0.13/0.40    (![A:$i,B:$i]:
% 0.13/0.40     ( ( v1_relat_1 @ B ) =>
% 0.13/0.40       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.13/0.40  thf('24', plain,
% 0.13/0.40      (![X16 : $i, X17 : $i]:
% 0.13/0.40         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.13/0.40          | ~ (v1_relat_1 @ X16))),
% 0.13/0.40      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.13/0.40  thf('25', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.13/0.40          | ~ (v1_relat_1 @ X0)
% 0.13/0.40          | ~ (v1_relat_1 @ X0))),
% 0.13/0.40      inference('sup+', [status(thm)], ['23', '24'])).
% 0.13/0.40  thf('26', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         (~ (v1_relat_1 @ X0)
% 0.13/0.40          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.13/0.40      inference('simplify', [status(thm)], ['25'])).
% 0.13/0.40  thf(d10_xboole_0, axiom,
% 0.13/0.40    (![A:$i,B:$i]:
% 0.13/0.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.13/0.40  thf('27', plain,
% 0.13/0.40      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.13/0.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.13/0.40  thf('28', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.13/0.40      inference('simplify', [status(thm)], ['27'])).
% 0.13/0.40  thf(t152_relat_1, axiom,
% 0.13/0.40    (![A:$i,B:$i]:
% 0.13/0.40     ( ( v1_relat_1 @ B ) =>
% 0.13/0.40       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.13/0.40            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.13/0.40            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.13/0.40  thf('29', plain,
% 0.13/0.40      (![X18 : $i, X19 : $i]:
% 0.13/0.40         (((X18) = (k1_xboole_0))
% 0.13/0.40          | ~ (v1_relat_1 @ X19)
% 0.13/0.40          | ~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.13/0.40          | ((k9_relat_1 @ X19 @ X18) != (k1_xboole_0)))),
% 0.13/0.40      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.13/0.40  thf('30', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) != (k1_xboole_0))
% 0.13/0.40          | ~ (v1_relat_1 @ X0)
% 0.13/0.40          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.13/0.40      inference('sup-', [status(thm)], ['28', '29'])).
% 0.13/0.40  thf('31', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.13/0.40          | ~ (v1_relat_1 @ X0)
% 0.13/0.40          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.13/0.40          | ~ (v1_relat_1 @ X0))),
% 0.13/0.40      inference('sup-', [status(thm)], ['26', '30'])).
% 0.13/0.40  thf('32', plain,
% 0.13/0.40      (![X0 : $i]:
% 0.13/0.40         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.13/0.40          | ~ (v1_relat_1 @ X0)
% 0.13/0.40          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 0.13/0.40      inference('simplify', [status(thm)], ['31'])).
% 0.13/0.40  thf('33', plain,
% 0.13/0.40      ((((k1_xboole_0) != (k1_xboole_0))
% 0.13/0.40        | ~ (v1_relat_1 @ sk_C)
% 0.13/0.40        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.13/0.40      inference('sup-', [status(thm)], ['22', '32'])).
% 0.13/0.40  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.13/0.40      inference('demod', [status(thm)], ['13', '14'])).
% 0.13/0.40  thf('35', plain,
% 0.13/0.40      ((((k1_xboole_0) != (k1_xboole_0))
% 0.13/0.40        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.13/0.40      inference('demod', [status(thm)], ['33', '34'])).
% 0.13/0.40  thf('36', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.13/0.40      inference('simplify', [status(thm)], ['35'])).
% 0.13/0.40  thf('37', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) != (k1_xboole_0))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf('38', plain,
% 0.13/0.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.13/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.40  thf(redefinition_k1_relset_1, axiom,
% 0.13/0.40    (![A:$i,B:$i,C:$i]:
% 0.13/0.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.13/0.40       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.13/0.40  thf('39', plain,
% 0.13/0.40      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.13/0.40         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.13/0.40          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.13/0.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.13/0.40  thf('40', plain,
% 0.13/0.40      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.13/0.40      inference('sup-', [status(thm)], ['38', '39'])).
% 0.13/0.40  thf('41', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.13/0.40      inference('demod', [status(thm)], ['37', '40'])).
% 0.13/0.40  thf('42', plain, ($false),
% 0.13/0.40      inference('simplify_reflect-', [status(thm)], ['36', '41'])).
% 0.13/0.40  
% 0.13/0.40  % SZS output end Refutation
% 0.13/0.40  
% 0.13/0.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
