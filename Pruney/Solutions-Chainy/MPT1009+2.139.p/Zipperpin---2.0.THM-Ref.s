%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CSxX1d9Z9g

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:09 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 123 expanded)
%              Number of leaves         :   40 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  537 (1192 expanded)
%              Number of equality atoms :   33 (  53 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ X28 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
       != ( k1_tarski @ X29 ) )
      | ( ( k2_relat_1 @ X30 )
        = ( k1_tarski @ ( k1_funct_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('32',plain,(
    ! [X38: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( sk_D @ X26 @ X24 @ X25 ) @ ( k1_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B_1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_D_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['4','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CSxX1d9Z9g
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 266 iterations in 0.167s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.63  thf(t64_funct_2, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.63         ( m1_subset_1 @
% 0.45/0.63           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.63       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.63         ( r1_tarski @
% 0.45/0.63           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.63           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.63            ( m1_subset_1 @
% 0.45/0.63              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.63          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.63            ( r1_tarski @
% 0.45/0.63              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.45/0.63              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (~ (r1_tarski @ 
% 0.45/0.63          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D_1 @ sk_C) @ 
% 0.45/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.45/0.63          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D_1 @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.45/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.63  thf(t144_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X27 : $i, X28 : $i]:
% 0.45/0.63         ((r1_tarski @ (k9_relat_1 @ X27 @ X28) @ (k2_relat_1 @ X27))
% 0.45/0.63          | ~ (v1_relat_1 @ X27))),
% 0.45/0.63      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.63         ((v4_relat_1 @ X31 @ X32)
% 0.45/0.63          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.63  thf('8', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.63  thf(d18_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X19 : $i, X20 : $i]:
% 0.45/0.63         (~ (v4_relat_1 @ X19 @ X20)
% 0.45/0.63          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.45/0.63          | ~ (v1_relat_1 @ X19))),
% 0.45/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.63        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.45/0.63          | (v1_relat_1 @ X17)
% 0.45/0.63          | ~ (v1_relat_1 @ X18))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.45/0.63        | (v1_relat_1 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf(fc6_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.63  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['10', '15'])).
% 0.45/0.63  thf(l3_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.45/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i]:
% 0.45/0.63         (((X15) = (k1_tarski @ X14))
% 0.45/0.63          | ((X15) = (k1_xboole_0))
% 0.45/0.63          | ~ (r1_tarski @ X15 @ (k1_tarski @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.45/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf(t14_funct_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.63       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.45/0.63         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X29 : $i, X30 : $i]:
% 0.45/0.63         (((k1_relat_1 @ X30) != (k1_tarski @ X29))
% 0.45/0.63          | ((k2_relat_1 @ X30) = (k1_tarski @ (k1_funct_1 @ X30 @ X29)))
% 0.45/0.63          | ~ (v1_funct_1 @ X30)
% 0.45/0.63          | ~ (v1_relat_1 @ X30))),
% 0.45/0.63      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 0.45/0.63          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | ~ (v1_funct_1 @ X0)
% 0.45/0.63          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.45/0.63        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.63        | ~ (v1_relat_1 @ sk_D_1)
% 0.45/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.45/0.63      inference('eq_res', [status(thm)], ['20'])).
% 0.45/0.63  thf('22', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.45/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (~ (r1_tarski @ 
% 0.45/0.63          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D_1 @ sk_C) @ 
% 0.45/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((~ (r1_tarski @ 
% 0.45/0.63           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D_1 @ sk_C) @ 
% 0.45/0.63           (k2_relat_1 @ sk_D_1))
% 0.45/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_D_1 @ X0)
% 0.45/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.45/0.63        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '28'])).
% 0.45/0.63  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('31', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.45/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.63  thf(t6_mcart_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.63                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.63                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.45/0.63                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.45/0.63                       ( r2_hidden @ G @ B ) ) =>
% 0.45/0.63                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X38 : $i]:
% 0.45/0.63         (((X38) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X38) @ X38))),
% 0.45/0.63      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.45/0.63  thf(t143_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ C ) =>
% 0.45/0.63       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.63         ( ?[D:$i]:
% 0.45/0.63           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.63             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.63             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 0.45/0.63          | (r2_hidden @ (sk_D @ X26 @ X24 @ X25) @ (k1_relat_1 @ X26))
% 0.45/0.63          | ~ (v1_relat_1 @ X26))),
% 0.45/0.63      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k9_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r2_hidden @ 
% 0.45/0.63             (sk_D @ X1 @ X0 @ (sk_B_1 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.63             (k1_relat_1 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf(d1_xboole_0, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X0)
% 0.45/0.63          | ((k9_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.45/0.63          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.63          | ((k9_relat_1 @ sk_D_1 @ X0) = (k1_xboole_0))
% 0.45/0.63          | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['31', '36'])).
% 0.45/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.63  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.63  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('40', plain, (![X0 : $i]: ((k9_relat_1 @ sk_D_1 @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.45/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.63  thf('41', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('42', plain, ($false),
% 0.45/0.63      inference('demod', [status(thm)], ['4', '40', '41'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
