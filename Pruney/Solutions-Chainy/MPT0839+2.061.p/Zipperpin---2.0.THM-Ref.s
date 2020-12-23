%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CkvKNztG3w

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 207 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  493 (2007 expanded)
%              Number of equality atoms :   31 (  81 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X11 ) @ ( sk_C @ X14 @ X11 ) ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('2',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X34 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('29',plain,(
    ! [X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['6','25'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','33'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CkvKNztG3w
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 95 iterations in 0.056s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('0', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf(d5_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X11 : $i, X14 : $i]:
% 0.20/0.51         (((X14) = (k2_relat_1 @ X11))
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ (sk_D @ X14 @ X11) @ (sk_C @ X14 @ X11)) @ X11)
% 0.20/0.51          | (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.51  thf(t50_relset_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.51               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51                    ( ![D:$i]:
% 0.20/0.51                      ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.51                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.51                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51                       ( ![D:$i]:
% 0.20/0.51                         ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.51                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X34 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X34 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X34 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X34 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X34 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X34 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X25 @ X26)
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('9', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf(t209_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.20/0.51          | ~ (v4_relat_1 @ X18 @ X19)
% 0.20/0.51          | ~ (v1_relat_1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.20/0.51          | (v1_relat_1 @ X7)
% 0.20/0.51          | ~ (v1_relat_1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.51  thf(t87_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X22)) @ X22)
% 0.20/0.51          | ~ (v1_relat_1 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X1)
% 0.20/0.51          | (m1_subset_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.20/0.51             (k1_zfmisc_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf(t4_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.51          | (m1_subset_1 @ X4 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X1)
% 0.20/0.51          | (m1_subset_1 @ X2 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.51          | (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.51  thf('24', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.51          | (m1_subset_1 @ X0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain, (![X34 : $i]: ~ (r2_hidden @ X34 @ (k1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['6', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_1)) @ X0)
% 0.20/0.51          | ((X0) = (k2_relat_1 @ (k1_relat_1 @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_1)) @ X0)
% 0.20/0.51          | ((X0) = (k2_relat_1 @ (k1_relat_1 @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '26'])).
% 0.20/0.51  thf('29', plain, (![X34 : $i]: ~ (r2_hidden @ X34 @ (k1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('clc', [status(thm)], ['6', '25'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_1)) @ X0)
% 0.20/0.51          | ((X0) = (k1_relat_1 @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['27', '30'])).
% 0.20/0.51  thf(t7_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) = (k1_relat_1 @ sk_C_1))
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '33'])).
% 0.20/0.51  thf(t65_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.51         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X20 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X20) != (k1_xboole_0))
% 0.20/0.51          | ((k2_relat_1 @ X20) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.51        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.51  thf('40', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.51         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.20/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '43'])).
% 0.20/0.51  thf('45', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['39', '44'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
