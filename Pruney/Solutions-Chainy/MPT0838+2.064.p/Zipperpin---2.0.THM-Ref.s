%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kovZVhub5h

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:07 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 105 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  491 ( 915 expanded)
%              Number of equality atoms :   34 (  51 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k3_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k3_tarski @ X2 ) )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['7','33'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kovZVhub5h
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:27:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 134 iterations in 0.083s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.54  thf(t7_xboole_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.54  thf(t49_relset_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54                    ( ![D:$i]:
% 0.36/0.54                      ( ( m1_subset_1 @ D @ B ) =>
% 0.36/0.54                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.54              ( ![C:$i]:
% 0.36/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54                       ( ![D:$i]:
% 0.36/0.54                         ( ( m1_subset_1 @ D @ B ) =>
% 0.36/0.54                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X33 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X33 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X33 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 0.36/0.54        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.36/0.54             sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.36/0.54         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.36/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.36/0.54        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc2_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.54         ((v5_relat_1 @ X24 @ X26)
% 0.36/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.54  thf('10', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf(d19_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         (~ (v5_relat_1 @ X19 @ X20)
% 0.36/0.54          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.36/0.54          | ~ (v1_relat_1 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc2_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.36/0.54          | (v1_relat_1 @ X17)
% 0.36/0.54          | ~ (v1_relat_1 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf(fc6_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.54  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.54  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '17'])).
% 0.36/0.54  thf(t3_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X14 : $i, X16 : $i]:
% 0.36/0.54         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf(t2_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         ((r2_hidden @ X12 @ X13)
% 0.36/0.54          | (v1_xboole_0 @ X13)
% 0.36/0.54          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.36/0.54        | (r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.54  thf(fc1_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.54  thf('23', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      ((r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.36/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.54  thf(d4_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.36/0.54       ( ![C:$i]:
% 0.36/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.54           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ X2)
% 0.36/0.54          | ~ (r2_hidden @ X3 @ X1)
% 0.36/0.54          | (r2_hidden @ X3 @ X4)
% 0.36/0.54          | ((X4) != (k3_tarski @ X2)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_tarski])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((r2_hidden @ X3 @ (k3_tarski @ X2))
% 0.36/0.54          | ~ (r2_hidden @ X3 @ X1)
% 0.36/0.54          | ~ (r2_hidden @ X1 @ X2))),
% 0.36/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((X0) = (k1_xboole_0))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ X1)
% 0.36/0.54          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['25', '27'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 0.36/0.54         (k3_tarski @ (k1_zfmisc_1 @ sk_B_1)))
% 0.36/0.54        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '28'])).
% 0.36/0.54  thf(t99_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.36/0.54  thf('30', plain, (![X8 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X8)) = (X8))),
% 0.36/0.54      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1)
% 0.36/0.54        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.54  thf(t1_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i]:
% 0.36/0.54         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.36/0.54        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.36/0.54      inference('clc', [status(thm)], ['7', '33'])).
% 0.36/0.54  thf(t65_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.54         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X23 : $i]:
% 0.36/0.54         (((k2_relat_1 @ X23) != (k1_xboole_0))
% 0.36/0.54          | ((k1_relat_1 @ X23) = (k1_xboole_0))
% 0.36/0.54          | ~ (v1_relat_1 @ X23))),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_C_1)
% 0.36/0.54        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.54        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.54  thf('39', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.54  thf('40', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.54         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.36/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.54  thf('44', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '43'])).
% 0.36/0.54  thf('45', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['39', '44'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
