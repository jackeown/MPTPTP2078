%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aTPeiVbvLm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:14 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 103 expanded)
%              Number of leaves         :   38 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  536 ( 921 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    r2_hidden @ sk_C_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B ) ),
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ~ ( v1_funct_2 @ X84 @ X82 @ X83 )
      | ( X82
        = ( k1_relset_1 @ X82 @ X83 @ X84 ) )
      | ~ ( zip_tseitin_2 @ X84 @ X83 @ X82 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X85: $i,X86: $i,X87: $i] :
      ( ~ ( zip_tseitin_1 @ X85 @ X86 )
      | ( zip_tseitin_2 @ X87 @ X85 @ X86 )
      | ~ ( m1_subset_1 @ X87 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X80: $i,X81: $i] :
      ( ( zip_tseitin_1 @ X80 @ X81 )
      | ( X80 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( r2_hidden @ X69 @ X70 )
      | ~ ( r1_tarski @ X70 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ( ( k1_relset_1 @ X78 @ X79 @ X77 )
        = ( k1_relat_1 @ X77 ) )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X78 @ X79 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','15','18'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X63: $i,X65: $i,X67: $i,X68: $i] :
      ( ( X65
       != ( k2_relat_1 @ X63 ) )
      | ( r2_hidden @ X67 @ X65 )
      | ~ ( r2_hidden @ X68 @ ( k1_relat_1 @ X63 ) )
      | ( X67
       != ( k1_funct_1 @ X63 @ X68 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X63: $i,X68: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( r2_hidden @ X68 @ ( k1_relat_1 @ X63 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X63 @ X68 ) @ ( k2_relat_1 @ X63 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( v1_relat_1 @ X71 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_3 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ( v5_relat_1 @ X74 @ X76 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( v5_relat_1 @ X60 @ X61 )
      | ( r1_tarski @ ( k2_relat_1 @ X60 ) @ X61 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_3 )
    = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_3 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aTPeiVbvLm
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.70/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.92  % Solved by: fo/fo7.sh
% 0.70/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.92  % done 460 iterations in 0.454s
% 0.70/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.92  % SZS output start Refutation
% 0.70/0.92  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.70/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.92  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.70/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.92  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.70/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.70/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.70/0.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.70/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.92  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.70/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.92  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.70/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.92  thf(t65_funct_2, conjecture,
% 0.70/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.70/0.92         ( m1_subset_1 @
% 0.70/0.92           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.70/0.92       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.70/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.92        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.70/0.92            ( m1_subset_1 @
% 0.70/0.92              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.70/0.92          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.70/0.92    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.70/0.92  thf('0', plain, ((r2_hidden @ sk_C_3 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(d1_funct_2, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.70/0.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.70/0.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.70/0.92  thf(zf_stmt_1, axiom,
% 0.70/0.92    (![C:$i,B:$i,A:$i]:
% 0.70/0.92     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.70/0.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.70/0.92  thf('2', plain,
% 0.70/0.92      (![X82 : $i, X83 : $i, X84 : $i]:
% 0.70/0.92         (~ (v1_funct_2 @ X84 @ X82 @ X83)
% 0.70/0.92          | ((X82) = (k1_relset_1 @ X82 @ X83 @ X84))
% 0.70/0.92          | ~ (zip_tseitin_2 @ X84 @ X83 @ X82))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.92  thf('3', plain,
% 0.70/0.92      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.70/0.92        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.92  thf('4', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.70/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.70/0.92  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.70/0.92  thf(zf_stmt_4, axiom,
% 0.70/0.92    (![B:$i,A:$i]:
% 0.70/0.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.92       ( zip_tseitin_1 @ B @ A ) ))).
% 0.70/0.92  thf(zf_stmt_5, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.70/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.70/0.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.70/0.92  thf('5', plain,
% 0.70/0.92      (![X85 : $i, X86 : $i, X87 : $i]:
% 0.70/0.92         (~ (zip_tseitin_1 @ X85 @ X86)
% 0.70/0.92          | (zip_tseitin_2 @ X87 @ X85 @ X86)
% 0.70/0.92          | ~ (m1_subset_1 @ X87 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X85))))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.70/0.92  thf('6', plain,
% 0.70/0.92      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.70/0.92        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.92  thf('7', plain,
% 0.70/0.92      (![X80 : $i, X81 : $i]:
% 0.70/0.92         ((zip_tseitin_1 @ X80 @ X81) | ((X80) = (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.70/0.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.92  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.70/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.92  thf('9', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.70/0.92      inference('sup+', [status(thm)], ['7', '8'])).
% 0.70/0.92  thf(d1_tarski, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.70/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.70/0.92  thf('10', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.92         (((X6) != (X5)) | (r2_hidden @ X6 @ X7) | ((X7) != (k1_tarski @ X5)))),
% 0.70/0.92      inference('cnf', [status(esa)], [d1_tarski])).
% 0.70/0.92  thf('11', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_tarski @ X5))),
% 0.70/0.92      inference('simplify', [status(thm)], ['10'])).
% 0.70/0.92  thf(t7_ordinal1, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.92  thf('12', plain,
% 0.70/0.92      (![X69 : $i, X70 : $i]:
% 0.70/0.92         (~ (r2_hidden @ X69 @ X70) | ~ (r1_tarski @ X70 @ X69))),
% 0.70/0.92      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.70/0.92  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.70/0.92      inference('sup-', [status(thm)], ['11', '12'])).
% 0.70/0.92  thf('14', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.70/0.92      inference('sup-', [status(thm)], ['9', '13'])).
% 0.70/0.92  thf('15', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.70/0.92      inference('demod', [status(thm)], ['6', '14'])).
% 0.70/0.92  thf('16', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.70/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(redefinition_k1_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.70/0.92  thf('17', plain,
% 0.70/0.92      (![X77 : $i, X78 : $i, X79 : $i]:
% 0.70/0.92         (((k1_relset_1 @ X78 @ X79 @ X77) = (k1_relat_1 @ X77))
% 0.70/0.92          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X78 @ X79))))),
% 0.70/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.92  thf('18', plain,
% 0.70/0.92      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.70/0.92         = (k1_relat_1 @ sk_D_2))),
% 0.70/0.92      inference('sup-', [status(thm)], ['16', '17'])).
% 0.70/0.92  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.70/0.92      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.70/0.92  thf(d5_funct_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.70/0.92           ( ![C:$i]:
% 0.70/0.92             ( ( r2_hidden @ C @ B ) <=>
% 0.70/0.92               ( ?[D:$i]:
% 0.70/0.92                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.70/0.92                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.70/0.92  thf('20', plain,
% 0.70/0.92      (![X63 : $i, X65 : $i, X67 : $i, X68 : $i]:
% 0.70/0.92         (((X65) != (k2_relat_1 @ X63))
% 0.70/0.92          | (r2_hidden @ X67 @ X65)
% 0.70/0.92          | ~ (r2_hidden @ X68 @ (k1_relat_1 @ X63))
% 0.70/0.92          | ((X67) != (k1_funct_1 @ X63 @ X68))
% 0.70/0.92          | ~ (v1_funct_1 @ X63)
% 0.70/0.92          | ~ (v1_relat_1 @ X63))),
% 0.70/0.92      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.70/0.92  thf('21', plain,
% 0.70/0.92      (![X63 : $i, X68 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X63)
% 0.70/0.92          | ~ (v1_funct_1 @ X63)
% 0.70/0.92          | ~ (r2_hidden @ X68 @ (k1_relat_1 @ X63))
% 0.70/0.92          | (r2_hidden @ (k1_funct_1 @ X63 @ X68) @ (k2_relat_1 @ X63)))),
% 0.70/0.92      inference('simplify', [status(thm)], ['20'])).
% 0.70/0.92  thf('22', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (r2_hidden @ X0 @ sk_A)
% 0.70/0.92          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.70/0.92          | ~ (v1_funct_1 @ sk_D_2)
% 0.70/0.92          | ~ (v1_relat_1 @ sk_D_2))),
% 0.70/0.92      inference('sup-', [status(thm)], ['19', '21'])).
% 0.70/0.92  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('24', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.70/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(cc1_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( v1_relat_1 @ C ) ))).
% 0.70/0.92  thf('25', plain,
% 0.70/0.92      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.70/0.92         ((v1_relat_1 @ X71)
% 0.70/0.92          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73))))),
% 0.70/0.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.70/0.92  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.70/0.92      inference('sup-', [status(thm)], ['24', '25'])).
% 0.70/0.92  thf('27', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (r2_hidden @ X0 @ sk_A)
% 0.70/0.92          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.70/0.92      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.70/0.92  thf('28', plain,
% 0.70/0.92      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_3) @ (k2_relat_1 @ sk_D_2))),
% 0.70/0.92      inference('sup-', [status(thm)], ['0', '27'])).
% 0.70/0.92  thf('29', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_D_2 @ 
% 0.70/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(cc2_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.70/0.92  thf('30', plain,
% 0.70/0.92      (![X74 : $i, X75 : $i, X76 : $i]:
% 0.70/0.92         ((v5_relat_1 @ X74 @ X76)
% 0.70/0.92          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76))))),
% 0.70/0.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.70/0.92  thf('31', plain, ((v5_relat_1 @ sk_D_2 @ (k1_tarski @ sk_B))),
% 0.70/0.92      inference('sup-', [status(thm)], ['29', '30'])).
% 0.70/0.92  thf(d19_relat_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ B ) =>
% 0.70/0.92       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.70/0.92  thf('32', plain,
% 0.70/0.92      (![X60 : $i, X61 : $i]:
% 0.70/0.92         (~ (v5_relat_1 @ X60 @ X61)
% 0.70/0.92          | (r1_tarski @ (k2_relat_1 @ X60) @ X61)
% 0.70/0.92          | ~ (v1_relat_1 @ X60))),
% 0.70/0.92      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.70/0.92  thf('33', plain,
% 0.70/0.92      ((~ (v1_relat_1 @ sk_D_2)
% 0.70/0.92        | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['31', '32'])).
% 0.70/0.92  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.70/0.92      inference('sup-', [status(thm)], ['24', '25'])).
% 0.70/0.92  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B))),
% 0.70/0.92      inference('demod', [status(thm)], ['33', '34'])).
% 0.70/0.92  thf(d3_tarski, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.92  thf('36', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.92         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.92          | (r2_hidden @ X0 @ X2)
% 0.70/0.92          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.92      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.92  thf('37', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.70/0.92          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['35', '36'])).
% 0.70/0.92  thf('38', plain,
% 0.70/0.92      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_3) @ (k1_tarski @ sk_B))),
% 0.70/0.92      inference('sup-', [status(thm)], ['28', '37'])).
% 0.70/0.92  thf('39', plain,
% 0.70/0.92      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.70/0.92         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.70/0.92      inference('cnf', [status(esa)], [d1_tarski])).
% 0.70/0.92  thf('40', plain,
% 0.70/0.92      (![X5 : $i, X8 : $i]:
% 0.70/0.92         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.70/0.92      inference('simplify', [status(thm)], ['39'])).
% 0.70/0.92  thf('41', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_3) = (sk_B))),
% 0.70/0.92      inference('sup-', [status(thm)], ['38', '40'])).
% 0.70/0.92  thf('42', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_3) != (sk_B))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('43', plain, ($false),
% 0.70/0.92      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.70/0.92  
% 0.70/0.92  % SZS output end Refutation
% 0.70/0.92  
% 0.70/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
