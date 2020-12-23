%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PrGVwv9qo8

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:01 EST 2020

% Result     : Theorem 30.92s
% Output     : Refutation 30.92s
% Verified   : 
% Statistics : Number of formulae       :   73 (  96 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  535 ( 973 expanded)
%              Number of equality atoms :   38 (  59 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ( X19
       != ( k2_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X20 @ X18 ) @ X20 ) @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k2_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_B @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_B @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

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

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_C_1 ) @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_C_1 ) @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['14','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PrGVwv9qo8
% 0.15/0.38  % Computer   : n023.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 13:37:36 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 30.92/31.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 30.92/31.10  % Solved by: fo/fo7.sh
% 30.92/31.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.92/31.10  % done 7981 iterations in 30.603s
% 30.92/31.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 30.92/31.10  % SZS output start Refutation
% 30.92/31.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.92/31.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.92/31.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 30.92/31.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.92/31.10  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 30.92/31.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.92/31.10  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 30.92/31.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.92/31.10  thf(sk_A_type, type, sk_A: $i).
% 30.92/31.10  thf(sk_B_type, type, sk_B: $i > $i).
% 30.92/31.10  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 30.92/31.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.92/31.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.92/31.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 30.92/31.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 30.92/31.10  thf(sk_C_1_type, type, sk_C_1: $i).
% 30.92/31.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.92/31.10  thf(t7_xboole_0, axiom,
% 30.92/31.10    (![A:$i]:
% 30.92/31.10     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 30.92/31.10          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 30.92/31.10  thf('0', plain,
% 30.92/31.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 30.92/31.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 30.92/31.10  thf(d5_relat_1, axiom,
% 30.92/31.10    (![A:$i,B:$i]:
% 30.92/31.10     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 30.92/31.10       ( ![C:$i]:
% 30.92/31.10         ( ( r2_hidden @ C @ B ) <=>
% 30.92/31.10           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 30.92/31.10  thf('1', plain,
% 30.92/31.10      (![X18 : $i, X19 : $i, X20 : $i]:
% 30.92/31.10         (~ (r2_hidden @ X20 @ X19)
% 30.92/31.10          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X20 @ X18) @ X20) @ X18)
% 30.92/31.10          | ((X19) != (k2_relat_1 @ X18)))),
% 30.92/31.10      inference('cnf', [status(esa)], [d5_relat_1])).
% 30.92/31.10  thf('2', plain,
% 30.92/31.10      (![X18 : $i, X20 : $i]:
% 30.92/31.10         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X20 @ X18) @ X20) @ X18)
% 30.92/31.10          | ~ (r2_hidden @ X20 @ (k2_relat_1 @ X18)))),
% 30.92/31.10      inference('simplify', [status(thm)], ['1'])).
% 30.92/31.10  thf('3', plain,
% 30.92/31.10      (![X0 : $i]:
% 30.92/31.10         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 30.92/31.10          | (r2_hidden @ 
% 30.92/31.10             (k4_tarski @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ X0)) @ X0) @ 
% 30.92/31.10              (sk_B @ (k2_relat_1 @ X0))) @ 
% 30.92/31.10             X0))),
% 30.92/31.10      inference('sup-', [status(thm)], ['0', '2'])).
% 30.92/31.10  thf('4', plain,
% 30.92/31.10      (![X0 : $i]:
% 30.92/31.10         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 30.92/31.10          | (r2_hidden @ 
% 30.92/31.10             (k4_tarski @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ X0)) @ X0) @ 
% 30.92/31.10              (sk_B @ (k2_relat_1 @ X0))) @ 
% 30.92/31.10             X0))),
% 30.92/31.10      inference('sup-', [status(thm)], ['0', '2'])).
% 30.92/31.10  thf(t49_relset_1, conjecture,
% 30.92/31.10    (![A:$i]:
% 30.92/31.10     ( ( ~( v1_xboole_0 @ A ) ) =>
% 30.92/31.10       ( ![B:$i]:
% 30.92/31.10         ( ( ~( v1_xboole_0 @ B ) ) =>
% 30.92/31.10           ( ![C:$i]:
% 30.92/31.10             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.10               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 30.92/31.10                    ( ![D:$i]:
% 30.92/31.10                      ( ( m1_subset_1 @ D @ B ) =>
% 30.92/31.10                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 30.92/31.10  thf(zf_stmt_0, negated_conjecture,
% 30.92/31.10    (~( ![A:$i]:
% 30.92/31.10        ( ( ~( v1_xboole_0 @ A ) ) =>
% 30.92/31.10          ( ![B:$i]:
% 30.92/31.10            ( ( ~( v1_xboole_0 @ B ) ) =>
% 30.92/31.10              ( ![C:$i]:
% 30.92/31.10                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.10                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 30.92/31.10                       ( ![D:$i]:
% 30.92/31.10                         ( ( m1_subset_1 @ D @ B ) =>
% 30.92/31.10                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 30.92/31.10    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 30.92/31.10  thf('5', plain,
% 30.92/31.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 30.92/31.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.10  thf(t4_subset, axiom,
% 30.92/31.10    (![A:$i,B:$i,C:$i]:
% 30.92/31.10     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 30.92/31.10       ( m1_subset_1 @ A @ C ) ))).
% 30.92/31.10  thf('6', plain,
% 30.92/31.10      (![X10 : $i, X11 : $i, X12 : $i]:
% 30.92/31.10         (~ (r2_hidden @ X10 @ X11)
% 30.92/31.10          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 30.92/31.10          | (m1_subset_1 @ X10 @ X12))),
% 30.92/31.10      inference('cnf', [status(esa)], [t4_subset])).
% 30.92/31.10  thf('7', plain,
% 30.92/31.10      (![X0 : $i]:
% 30.92/31.10         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 30.92/31.10          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['5', '6'])).
% 30.92/31.10  thf('8', plain,
% 30.92/31.10      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 30.92/31.10        | (m1_subset_1 @ 
% 30.92/31.10           (k4_tarski @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_C_1) @ 
% 30.92/31.10            (sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 30.92/31.10           (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 30.92/31.10      inference('sup-', [status(thm)], ['4', '7'])).
% 30.92/31.10  thf(t2_subset, axiom,
% 30.92/31.10    (![A:$i,B:$i]:
% 30.92/31.10     ( ( m1_subset_1 @ A @ B ) =>
% 30.92/31.10       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 30.92/31.10  thf('9', plain,
% 30.92/31.10      (![X8 : $i, X9 : $i]:
% 30.92/31.10         ((r2_hidden @ X8 @ X9)
% 30.92/31.10          | (v1_xboole_0 @ X9)
% 30.92/31.10          | ~ (m1_subset_1 @ X8 @ X9))),
% 30.92/31.10      inference('cnf', [status(esa)], [t2_subset])).
% 30.92/31.10  thf('10', plain,
% 30.92/31.10      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 30.92/31.10        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 30.92/31.10        | (r2_hidden @ 
% 30.92/31.10           (k4_tarski @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_C_1) @ 
% 30.92/31.10            (sk_B @ (k2_relat_1 @ sk_C_1))) @ 
% 30.92/31.10           (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 30.92/31.10      inference('sup-', [status(thm)], ['8', '9'])).
% 30.92/31.10  thf(l54_zfmisc_1, axiom,
% 30.92/31.10    (![A:$i,B:$i,C:$i,D:$i]:
% 30.92/31.10     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 30.92/31.10       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 30.92/31.10  thf('11', plain,
% 30.92/31.10      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 30.92/31.10         ((r2_hidden @ X3 @ X4)
% 30.92/31.10          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X4)))),
% 30.92/31.10      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 30.92/31.10  thf('12', plain,
% 30.92/31.10      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 30.92/31.10        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 30.92/31.10        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['10', '11'])).
% 30.92/31.10  thf(t1_subset, axiom,
% 30.92/31.10    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 30.92/31.10  thf('13', plain,
% 30.92/31.10      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 30.92/31.10      inference('cnf', [status(esa)], [t1_subset])).
% 30.92/31.10  thf('14', plain,
% 30.92/31.10      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 30.92/31.10        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 30.92/31.10        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['12', '13'])).
% 30.92/31.10  thf('15', plain,
% 30.92/31.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 30.92/31.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 30.92/31.10  thf('16', plain,
% 30.92/31.10      (![X33 : $i]:
% 30.92/31.10         (~ (r2_hidden @ X33 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 30.92/31.10          | ~ (m1_subset_1 @ X33 @ sk_B_1))),
% 30.92/31.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.10  thf('17', plain,
% 30.92/31.10      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 30.92/31.10        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 30.92/31.10             sk_B_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['15', '16'])).
% 30.92/31.10  thf('18', plain,
% 30.92/31.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 30.92/31.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.10  thf(redefinition_k2_relset_1, axiom,
% 30.92/31.10    (![A:$i,B:$i,C:$i]:
% 30.92/31.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 30.92/31.10  thf('19', plain,
% 30.92/31.10      (![X30 : $i, X31 : $i, X32 : $i]:
% 30.92/31.10         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 30.92/31.10          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 30.92/31.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 30.92/31.10  thf('20', plain,
% 30.92/31.10      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['18', '19'])).
% 30.92/31.10  thf('21', plain,
% 30.92/31.10      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['18', '19'])).
% 30.92/31.10  thf('22', plain,
% 30.92/31.10      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 30.92/31.10        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 30.92/31.10      inference('demod', [status(thm)], ['17', '20', '21'])).
% 30.92/31.10  thf('23', plain,
% 30.92/31.10      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 30.92/31.10        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 30.92/31.10      inference('clc', [status(thm)], ['14', '22'])).
% 30.92/31.10  thf('24', plain,
% 30.92/31.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 30.92/31.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.10  thf(t5_subset, axiom,
% 30.92/31.10    (![A:$i,B:$i,C:$i]:
% 30.92/31.10     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 30.92/31.10          ( v1_xboole_0 @ C ) ) ))).
% 30.92/31.10  thf('25', plain,
% 30.92/31.10      (![X13 : $i, X14 : $i, X15 : $i]:
% 30.92/31.10         (~ (r2_hidden @ X13 @ X14)
% 30.92/31.10          | ~ (v1_xboole_0 @ X15)
% 30.92/31.10          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 30.92/31.10      inference('cnf', [status(esa)], [t5_subset])).
% 30.92/31.10  thf('26', plain,
% 30.92/31.10      (![X0 : $i]:
% 30.92/31.10         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 30.92/31.10          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['24', '25'])).
% 30.92/31.10  thf('27', plain,
% 30.92/31.10      (![X0 : $i]:
% 30.92/31.10         (((k2_relat_1 @ sk_C_1) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['23', '26'])).
% 30.92/31.10  thf('28', plain,
% 30.92/31.10      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 30.92/31.10        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 30.92/31.10      inference('sup-', [status(thm)], ['3', '27'])).
% 30.92/31.10  thf('29', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 30.92/31.10      inference('simplify', [status(thm)], ['28'])).
% 30.92/31.10  thf(t65_relat_1, axiom,
% 30.92/31.10    (![A:$i]:
% 30.92/31.10     ( ( v1_relat_1 @ A ) =>
% 30.92/31.10       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 30.92/31.10         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 30.92/31.10  thf('30', plain,
% 30.92/31.10      (![X23 : $i]:
% 30.92/31.10         (((k2_relat_1 @ X23) != (k1_xboole_0))
% 30.92/31.10          | ((k1_relat_1 @ X23) = (k1_xboole_0))
% 30.92/31.10          | ~ (v1_relat_1 @ X23))),
% 30.92/31.10      inference('cnf', [status(esa)], [t65_relat_1])).
% 30.92/31.10  thf('31', plain,
% 30.92/31.10      ((((k1_xboole_0) != (k1_xboole_0))
% 30.92/31.10        | ~ (v1_relat_1 @ sk_C_1)
% 30.92/31.10        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 30.92/31.10      inference('sup-', [status(thm)], ['29', '30'])).
% 30.92/31.10  thf('32', plain,
% 30.92/31.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 30.92/31.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.10  thf(cc1_relset_1, axiom,
% 30.92/31.10    (![A:$i,B:$i,C:$i]:
% 30.92/31.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.10       ( v1_relat_1 @ C ) ))).
% 30.92/31.10  thf('33', plain,
% 30.92/31.10      (![X24 : $i, X25 : $i, X26 : $i]:
% 30.92/31.10         ((v1_relat_1 @ X24)
% 30.92/31.10          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 30.92/31.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.92/31.10  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 30.92/31.10      inference('sup-', [status(thm)], ['32', '33'])).
% 30.92/31.10  thf('35', plain,
% 30.92/31.10      ((((k1_xboole_0) != (k1_xboole_0))
% 30.92/31.10        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 30.92/31.10      inference('demod', [status(thm)], ['31', '34'])).
% 30.92/31.10  thf('36', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 30.92/31.10      inference('simplify', [status(thm)], ['35'])).
% 30.92/31.10  thf('37', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 30.92/31.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.10  thf('38', plain,
% 30.92/31.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 30.92/31.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.92/31.10  thf(redefinition_k1_relset_1, axiom,
% 30.92/31.10    (![A:$i,B:$i,C:$i]:
% 30.92/31.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.92/31.10       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 30.92/31.10  thf('39', plain,
% 30.92/31.10      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.92/31.10         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 30.92/31.10          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 30.92/31.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 30.92/31.10  thf('40', plain,
% 30.92/31.10      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 30.92/31.10      inference('sup-', [status(thm)], ['38', '39'])).
% 30.92/31.10  thf('41', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 30.92/31.10      inference('demod', [status(thm)], ['37', '40'])).
% 30.92/31.10  thf('42', plain, ($false),
% 30.92/31.10      inference('simplify_reflect-', [status(thm)], ['36', '41'])).
% 30.92/31.10  
% 30.92/31.10  % SZS output end Refutation
% 30.92/31.10  
% 30.94/31.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
