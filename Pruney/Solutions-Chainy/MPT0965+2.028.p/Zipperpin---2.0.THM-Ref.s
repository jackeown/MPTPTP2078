%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bhUCnS21JC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:01 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 117 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  534 (1112 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X20 )
       != X18 )
      | ~ ( r2_hidden @ X21 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_E @ X21 @ X20 ) ) @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_A != sk_A ) ) ),
    inference(demod,[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ ( sk_E @ sk_C_1 @ sk_D_1 ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['1','17'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( r2_hidden @ sk_C_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_C_1 @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','25','26'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('39',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bhUCnS21JC
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.35  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 80 iterations in 0.095s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.40/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(t7_funct_2, conjecture,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58       ( ( r2_hidden @ C @ A ) =>
% 0.40/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.58            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58          ( ( r2_hidden @ C @ A ) =>
% 0.40/0.58            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.40/0.58  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t22_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.40/0.58       ( ( ![D:$i]:
% 0.40/0.58           ( ~( ( r2_hidden @ D @ B ) & 
% 0.40/0.58                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.40/0.58         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X18 @ X19 @ X20) != (X18))
% 0.40/0.58          | ~ (r2_hidden @ X21 @ X18)
% 0.40/0.58          | (r2_hidden @ (k4_tarski @ X21 @ (sk_E @ X21 @ X20)) @ X20)
% 0.40/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.40/0.58      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.58          | ((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) != (sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d1_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_1, axiom,
% 0.40/0.58    (![C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.58         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.40/0.58          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.40/0.58          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.40/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf(zf_stmt_2, axiom,
% 0.40/0.58    (![B:$i,A:$i]:
% 0.40/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X23 : $i, X24 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_5, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.58         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.40/0.58          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.40/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.40/0.58        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.40/0.58  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('14', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('15', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['7', '14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.58          | ((sk_A) != (sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '15'])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.58          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1))),
% 0.40/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      ((r2_hidden @ (k4_tarski @ sk_C_1 @ (sk_E @ sk_C_1 @ sk_D_1)) @ sk_D_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '17'])).
% 0.40/0.58  thf(t8_funct_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.58       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.40/0.58         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.40/0.58           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.58         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.40/0.58          | (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.40/0.58          | ~ (v1_funct_1 @ X13)
% 0.40/0.58          | ~ (v1_relat_1 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_D_1)
% 0.40/0.58        | ~ (v1_funct_1 @ sk_D_1)
% 0.40/0.58        | (r2_hidden @ sk_C_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X4 : $i, X5 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.40/0.58          | (v1_relat_1 @ X4)
% 0.40/0.58          | ~ (v1_relat_1 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf(fc6_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.58  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('26', plain, ((v1_funct_1 @ sk_D_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('27', plain, ((r2_hidden @ sk_C_1 @ (k1_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['20', '25', '26'])).
% 0.40/0.58  thf(t12_funct_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.58       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.58         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.40/0.58          | (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ (k2_relat_1 @ X11))
% 0.40/0.58          | ~ (v1_funct_1 @ X11)
% 0.40/0.58          | ~ (v1_relat_1 @ X11))),
% 0.40/0.58      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_D_1)
% 0.40/0.58        | ~ (v1_funct_1 @ sk_D_1)
% 0.40/0.58        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.58  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.58         ((v5_relat_1 @ X15 @ X17)
% 0.40/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.58  thf('35', plain, ((v5_relat_1 @ sk_D_1 @ sk_B)),
% 0.40/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.58  thf(d19_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         (~ (v5_relat_1 @ X6 @ X7)
% 0.40/0.58          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.40/0.58          | ~ (v1_relat_1 @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.58  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.40/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('39', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_B)),
% 0.40/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.40/0.58  thf(d3_tarski, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.58          | (r2_hidden @ X0 @ X2)
% 0.40/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain, ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ sk_B)),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '41'])).
% 0.40/0.58  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
