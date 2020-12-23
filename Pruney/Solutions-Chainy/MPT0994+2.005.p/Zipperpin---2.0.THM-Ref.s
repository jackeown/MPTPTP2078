%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TkTcXRq7aj

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:52 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 120 expanded)
%              Number of leaves         :   36 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  621 (1577 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t41_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( r2_hidden @ C @ A )
          & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C )
            = ( k1_funct_1 @ E @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( ( v1_funct_1 @ E )
          & ( v1_funct_2 @ E @ A @ B )
          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( r2_hidden @ C @ A )
            & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) )
         => ( ( B = k1_xboole_0 )
            | ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C )
              = ( k1_funct_1 @ E @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_funct_2])).

thf('0',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_E_1 @ sk_C ) @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X19 )
       != X17 )
      | ~ ( r2_hidden @ X20 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_E @ X20 @ X19 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_E_1 ) ) @ sk_E_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_relset_1 @ sk_A @ sk_B @ sk_E_1 )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_E_1 @ sk_A @ sk_B ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_E_1 ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_E_1 ) ) @ sk_E_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_A != sk_A ) ) ),
    inference(demod,[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_E_1 ) ) @ sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( sk_E @ sk_C @ sk_E_1 ) ) @ sk_E_1 ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['20','25','26'])).

thf(t86_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X5 @ X4 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ ( k8_relat_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t86_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_E_1 ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_E_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('31',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_E_1 ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_E_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ sk_D_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf(t87_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X8 @ X9 ) @ X7 )
        = ( k1_funct_1 @ X9 @ X7 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t87_funct_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('37',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ( k1_funct_1 @ ( k6_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_E_1 ) @ sk_C )
 != ( k1_funct_1 @ sk_E_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k6_relset_1 @ X15 @ X16 @ X13 @ X14 )
        = ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_E_1 )
      = ( k8_relat_1 @ X0 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
 != ( k1_funct_1 @ sk_E_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TkTcXRq7aj
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 82 iterations in 0.092s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.36/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.54  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.36/0.54  thf(t41_funct_2, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.36/0.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) ) =>
% 0.36/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.54           ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C ) =
% 0.36/0.54             ( k1_funct_1 @ E @ C ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.54        ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.36/0.54            ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54          ( ( ( r2_hidden @ C @ A ) & 
% 0.36/0.54              ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) ) =>
% 0.36/0.54            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.54              ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C ) =
% 0.36/0.54                ( k1_funct_1 @ E @ C ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t41_funct_2])).
% 0.36/0.54  thf('0', plain, ((r2_hidden @ (k1_funct_1 @ sk_E_1 @ sk_C) @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t22_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.54       ( ( ![D:$i]:
% 0.36/0.54           ( ~( ( r2_hidden @ D @ B ) & 
% 0.36/0.54                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.36/0.54         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.54         (((k1_relset_1 @ X17 @ X18 @ X19) != (X17))
% 0.36/0.54          | ~ (r2_hidden @ X20 @ X17)
% 0.36/0.54          | (r2_hidden @ (k4_tarski @ X20 @ (sk_E @ X20 @ X19)) @ X19)
% 0.36/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.36/0.54      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_E_1)) @ sk_E_1)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.54          | ((k1_relset_1 @ sk_A @ sk_B @ sk_E_1) != (sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf('5', plain, ((v1_funct_2 @ sk_E_1 @ sk_A @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d1_funct_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, axiom,
% 0.36/0.54    (![C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.54         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.36/0.54          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.36/0.54          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((~ (zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A)
% 0.36/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_E_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf(zf_stmt_2, axiom,
% 0.36/0.54    (![B:$i,A:$i]:
% 0.36/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X22 : $i, X23 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_5, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.54         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.36/0.54          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.36/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (((zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A)
% 0.36/0.54        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '11'])).
% 0.36/0.54  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('14', plain, ((zip_tseitin_1 @ sk_E_1 @ sk_B @ sk_A)),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_E_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_E_1)) @ sk_E_1)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.54          | ((sk_A) != (sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['4', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_E_1)) @ sk_E_1))),
% 0.36/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((r2_hidden @ (k4_tarski @ sk_C @ (sk_E @ sk_C @ sk_E_1)) @ sk_E_1)),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '17'])).
% 0.36/0.54  thf(t8_funct_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.36/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.54           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.36/0.54          | (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.36/0.54          | ~ (v1_funct_1 @ X11)
% 0.36/0.54          | ~ (v1_relat_1 @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_E_1)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_E_1)
% 0.36/0.54        | (r2_hidden @ sk_C @ (k1_relat_1 @ sk_E_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc2_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.54          | (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_E_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf(fc6_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.54  thf('25', plain, ((v1_relat_1 @ sk_E_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('26', plain, ((v1_funct_1 @ sk_E_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('27', plain, ((r2_hidden @ sk_C @ (k1_relat_1 @ sk_E_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['20', '25', '26'])).
% 0.36/0.54  thf(t86_funct_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.36/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.54           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X4 @ (k1_relat_1 @ X5))
% 0.36/0.54          | ~ (r2_hidden @ (k1_funct_1 @ X5 @ X4) @ X6)
% 0.36/0.54          | (r2_hidden @ X4 @ (k1_relat_1 @ (k8_relat_1 @ X6 @ X5)))
% 0.36/0.54          | ~ (v1_funct_1 @ X5)
% 0.36/0.54          | ~ (v1_relat_1 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t86_funct_1])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ sk_E_1)
% 0.36/0.54          | ~ (v1_funct_1 @ sk_E_1)
% 0.36/0.54          | (r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_E_1)))
% 0.36/0.54          | ~ (r2_hidden @ (k1_funct_1 @ sk_E_1 @ sk_C) @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain, ((v1_relat_1 @ sk_E_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('31', plain, ((v1_funct_1 @ sk_E_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_E_1)))
% 0.36/0.54          | ~ (r2_hidden @ (k1_funct_1 @ sk_E_1 @ sk_C) @ X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ sk_D_1 @ sk_E_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '32'])).
% 0.36/0.54  thf(t87_funct_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.36/0.54         ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X7 @ (k1_relat_1 @ (k8_relat_1 @ X8 @ X9)))
% 0.36/0.54          | ((k1_funct_1 @ (k8_relat_1 @ X8 @ X9) @ X7)
% 0.36/0.54              = (k1_funct_1 @ X9 @ X7))
% 0.36/0.54          | ~ (v1_funct_1 @ X9)
% 0.36/0.54          | ~ (v1_relat_1 @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [t87_funct_1])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_E_1)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_E_1)
% 0.36/0.54        | ((k1_funct_1 @ (k8_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.36/0.54            = (k1_funct_1 @ sk_E_1 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.54  thf('36', plain, ((v1_relat_1 @ sk_E_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('37', plain, ((v1_funct_1 @ sk_E_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (((k1_funct_1 @ (k8_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.36/0.54         = (k1_funct_1 @ sk_E_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (((k1_funct_1 @ (k6_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.36/0.54         != (k1_funct_1 @ sk_E_1 @ sk_C))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k6_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.54         (((k6_relset_1 @ X15 @ X16 @ X13 @ X14) = (k8_relat_1 @ X13 @ X14))
% 0.36/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_E_1)
% 0.36/0.54           = (k8_relat_1 @ X0 @ sk_E_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((k1_funct_1 @ (k8_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.36/0.54         != (k1_funct_1 @ sk_E_1 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['39', '42'])).
% 0.36/0.54  thf('44', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['38', '43'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
