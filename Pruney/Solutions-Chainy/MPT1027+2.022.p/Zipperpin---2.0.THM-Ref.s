%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TCn7ZPsPlA

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 244 expanded)
%              Number of leaves         :   30 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  571 (3058 expanded)
%              Number of equality atoms :   53 ( 164 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','7','8'])).

thf('10',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','9'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','9'])).

thf('21',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X29 ) @ X28 )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('26',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('30',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('32',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['26','27','29','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['26','27','29','30','31'])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['38','39'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('41',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('43',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['50','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['33','42','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TCn7ZPsPlA
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:42:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 122 iterations in 0.057s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(t130_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.50         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.50           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.20/0.50            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.50              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.50        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.20/0.50         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('4', plain, (((v1_funct_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.20/0.50       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.20/0.50       ~ ((v1_funct_1 @ sk_C))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('9', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['4', '7', '8'])).
% 0.20/0.50  thf('10', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '9'])).
% 0.20/0.50  thf(d1_funct_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, axiom,
% 0.20/0.50    (![B:$i,A:$i]:
% 0.20/0.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.50       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X33 : $i, X34 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_5, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.50         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.20/0.50          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.20/0.50          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.50  thf('16', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.50         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 0.20/0.50          | (v1_funct_2 @ X37 @ X35 @ X36)
% 0.20/0.50          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((((sk_A) != (sk_A))
% 0.20/0.50        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.20/0.50        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.50        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.50  thf('20', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '9'])).
% 0.20/0.50  thf('21', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.50  thf('23', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t162_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X28 : $i, X29 : $i]:
% 0.20/0.50         (((k9_relat_1 @ (k6_relat_1 @ X29) @ X28) = (X28))
% 0.20/0.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((k9_relat_1 @ (k6_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_C)
% 0.20/0.50         = (sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.50  thf('30', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.50  thf(t150_relat_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X18 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.20/0.50  thf('32', plain, (((k1_xboole_0) = (sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '29', '30', '31'])).
% 0.20/0.50  thf('33', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.50         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.20/0.50          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain, (((k1_xboole_0) = (sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '29', '30', '31'])).
% 0.20/0.50  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf(t60_relat_1, axiom,
% 0.20/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('41', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf(t4_subset_1, axiom,
% 0.20/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.50         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.20/0.50          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.50         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 0.20/0.50          | (v1_funct_2 @ X37 @ X35 @ X36)
% 0.20/0.50          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X1) != (k1_xboole_0))
% 0.20/0.50          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.50          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X33 : $i, X34 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('52', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 0.20/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.50         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.20/0.50          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.20/0.50          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '55'])).
% 0.20/0.50  thf('57', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.50      inference('simplify_reflect+', [status(thm)], ['50', '56'])).
% 0.20/0.50  thf('58', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '42', '57'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
