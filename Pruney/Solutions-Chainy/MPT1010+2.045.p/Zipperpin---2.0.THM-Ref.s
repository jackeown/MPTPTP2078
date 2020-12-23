%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hjLBPl36ki

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 233 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  532 (2798 expanded)
%              Number of equality atoms :   45 ( 194 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X31 @ X28 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('15',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t2_setfam_1,axiom,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('16',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_setfam_1])).

thf('17',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('23',plain,(
    v5_relat_1 @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X20 @ X19 ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v5_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ X0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ X0 )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('38',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('39',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ k1_xboole_0 )
      | ( ( k1_funct_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('44',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ sk_D @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['18','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hjLBPl36ki
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:17:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 77 iterations in 0.045s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(t65_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.51       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.51            ( m1_subset_1 @
% 0.21/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.51          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.51  thf('0', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t7_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X28 @ X29)
% 0.21/0.51          | ((X30) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_funct_1 @ X31)
% 0.21/0.51          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.21/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.21/0.51          | (r2_hidden @ (k1_funct_1 @ X31 @ X28) @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.51  thf(d1_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i]:
% 0.21/0.51         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51        | ((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.51  thf('12', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t11_setfam_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.51  thf('14', plain, (![X12 : $i]: ((k1_setfam_1 @ (k1_tarski @ X12)) = (X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.21/0.51  thf('15', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf(t2_setfam_1, axiom, (( k1_setfam_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.51  thf('16', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_setfam_1])).
% 0.21/0.51  thf('17', plain, (((k1_xboole_0) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X25 @ X27)
% 0.21/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('21', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('23', plain, ((v5_relat_1 @ sk_D @ k1_xboole_0)),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf(d4_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i,C:$i]:
% 0.21/0.51         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.51             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.51               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.51           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.51             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.51               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         ((r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.21/0.51          | ((X17) = (k1_xboole_0))
% 0.21/0.51          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 0.21/0.51          | ~ (v1_funct_1 @ X16)
% 0.21/0.51          | ~ (v1_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X16)
% 0.21/0.51          | ~ (v1_funct_1 @ X16)
% 0.21/0.51          | ((k1_funct_1 @ X16 @ X15) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.51  thf(t176_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.21/0.51         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.21/0.51          | (m1_subset_1 @ (k1_funct_1 @ X20 @ X19) @ X21)
% 0.21/0.51          | ~ (v1_funct_1 @ X20)
% 0.21/0.51          | ~ (v5_relat_1 @ X20 @ X21)
% 0.21/0.51          | ~ (v1_relat_1 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v5_relat_1 @ X0 @ X2)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | (m1_subset_1 @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.21/0.51          | ~ (v5_relat_1 @ X0 @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_funct_1 @ sk_D @ X0) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | ~ (v1_relat_1 @ sk_D)
% 0.21/0.51          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.51  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_funct_1 @ sk_D @ X0) = (k1_xboole_0))
% 0.21/0.51          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.21/0.51  thf(t2_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         ((r2_hidden @ X13 @ X14)
% 0.21/0.51          | (v1_xboole_0 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_funct_1 @ sk_D @ X0) = (k1_xboole_0))
% 0.21/0.51          | (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('38', plain, (((k1_xboole_0) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('39', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.51  thf('40', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.51  thf('41', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ k1_xboole_0)
% 0.21/0.51          | ((k1_funct_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['36', '41'])).
% 0.21/0.51  thf('43', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X0 : $i, X3 : $i]:
% 0.21/0.51         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain, (![X0 : $i]: ((k1_funct_1 @ sk_D @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('clc', [status(thm)], ['42', '45'])).
% 0.21/0.51  thf('47', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '46'])).
% 0.21/0.51  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
