%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZykD1wZo9I

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 100 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  536 (1298 expanded)
%              Number of equality atoms :   34 (  78 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t21_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E ) )
           => ( ( r2_hidden @ C @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                  = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X12 )
       != X10 )
      | ~ ( r2_hidden @ X13 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_E @ X13 @ X12 ) ) @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_A != sk_A ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_1 ) ) @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( sk_E @ sk_C @ sk_D_1 ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X8 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k1_funct_1 @ X4 @ ( k1_funct_1 @ X5 @ X6 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ X0 ) @ sk_C )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ X0 ) @ sk_C )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E_1 ) @ sk_C )
 != ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
     != ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_E_1 )
    | ~ ( v1_funct_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) )
 != ( k1_funct_1 @ sk_E_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZykD1wZo9I
% 0.13/0.37  % Computer   : n022.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 11:54:11 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.56  % Solved by: fo/fo7.sh
% 0.23/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.56  % done 62 iterations in 0.072s
% 0.23/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.56  % SZS output start Refutation
% 0.23/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.23/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.56  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.23/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.23/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.56  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.23/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.23/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.56  thf(t21_funct_2, conjecture,
% 0.23/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.56       ( ![E:$i]:
% 0.23/0.56         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.23/0.56           ( ( r2_hidden @ C @ A ) =>
% 0.23/0.56             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.56               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.23/0.56                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.23/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.56          ( ![E:$i]:
% 0.23/0.56            ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.23/0.56              ( ( r2_hidden @ C @ A ) =>
% 0.23/0.56                ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.56                  ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.23/0.56                    ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ) )),
% 0.23/0.56    inference('cnf.neg', [status(esa)], [t21_funct_2])).
% 0.23/0.56  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('1', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(t22_relset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.23/0.56       ( ( ![D:$i]:
% 0.23/0.56           ( ~( ( r2_hidden @ D @ B ) & 
% 0.23/0.56                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.23/0.56         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.23/0.56  thf('2', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.56         (((k1_relset_1 @ X10 @ X11 @ X12) != (X10))
% 0.23/0.56          | ~ (r2_hidden @ X13 @ X10)
% 0.23/0.56          | (r2_hidden @ (k4_tarski @ X13 @ (sk_E @ X13 @ X12)) @ X12)
% 0.23/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.23/0.56      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.23/0.56  thf('3', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1)
% 0.23/0.56          | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.56          | ((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) != (sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.56  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(d1_funct_2, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.23/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.23/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.23/0.56  thf(zf_stmt_1, axiom,
% 0.23/0.56    (![C:$i,B:$i,A:$i]:
% 0.23/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.23/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.23/0.56  thf('5', plain,
% 0.23/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.56         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.23/0.56          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.23/0.56          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.23/0.56  thf('6', plain,
% 0.23/0.56      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.23/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.56  thf(zf_stmt_2, axiom,
% 0.23/0.56    (![B:$i,A:$i]:
% 0.23/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.23/0.56  thf('7', plain,
% 0.23/0.56      (![X15 : $i, X16 : $i]:
% 0.23/0.56         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.56  thf('8', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.23/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.23/0.56  thf(zf_stmt_5, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.23/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.23/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.23/0.56  thf('9', plain,
% 0.23/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.56         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.23/0.56          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.23/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.23/0.56  thf('10', plain,
% 0.23/0.56      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.23/0.56        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.56  thf('11', plain,
% 0.23/0.56      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.23/0.56  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('13', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.23/0.56      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.23/0.56  thf('14', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['6', '13'])).
% 0.23/0.56  thf('15', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1)
% 0.23/0.56          | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.56          | ((sk_A) != (sk_A)))),
% 0.23/0.56      inference('demod', [status(thm)], ['3', '14'])).
% 0.23/0.56  thf('16', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_1)) @ sk_D_1))),
% 0.23/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.56  thf('17', plain,
% 0.23/0.56      ((r2_hidden @ (k4_tarski @ sk_C @ (sk_E @ sk_C @ sk_D_1)) @ sk_D_1)),
% 0.23/0.56      inference('sup-', [status(thm)], ['0', '16'])).
% 0.23/0.56  thf(t8_funct_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.23/0.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.23/0.56           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.23/0.56  thf('18', plain,
% 0.23/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.56         (~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X8)
% 0.23/0.56          | (r2_hidden @ X7 @ (k1_relat_1 @ X8))
% 0.23/0.56          | ~ (v1_funct_1 @ X8)
% 0.23/0.56          | ~ (v1_relat_1 @ X8))),
% 0.23/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.23/0.56  thf('19', plain,
% 0.23/0.56      ((~ (v1_relat_1 @ sk_D_1)
% 0.23/0.56        | ~ (v1_funct_1 @ sk_D_1)
% 0.23/0.56        | (r2_hidden @ sk_C @ (k1_relat_1 @ sk_D_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.56  thf('20', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(cc2_relat_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( v1_relat_1 @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.56  thf('21', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.23/0.56          | (v1_relat_1 @ X0)
% 0.23/0.56          | ~ (v1_relat_1 @ X1))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.56  thf('22', plain,
% 0.23/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.56  thf(fc6_relat_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.56  thf('23', plain,
% 0.23/0.56      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.23/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.56  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.56  thf('25', plain, ((v1_funct_1 @ sk_D_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('26', plain, ((r2_hidden @ sk_C @ (k1_relat_1 @ sk_D_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.23/0.56  thf(t23_funct_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.56       ( ![C:$i]:
% 0.23/0.56         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.56           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.23/0.56             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.23/0.56               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.23/0.56  thf('27', plain,
% 0.23/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.56         (~ (v1_relat_1 @ X4)
% 0.23/0.56          | ~ (v1_funct_1 @ X4)
% 0.23/0.56          | ((k1_funct_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 0.23/0.56              = (k1_funct_1 @ X4 @ (k1_funct_1 @ X5 @ X6)))
% 0.23/0.56          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X5))
% 0.23/0.56          | ~ (v1_funct_1 @ X5)
% 0.23/0.56          | ~ (v1_relat_1 @ X5))),
% 0.23/0.56      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.23/0.56  thf('28', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (~ (v1_relat_1 @ sk_D_1)
% 0.23/0.56          | ~ (v1_funct_1 @ sk_D_1)
% 0.23/0.56          | ((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ X0) @ sk_C)
% 0.23/0.56              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.23/0.56          | ~ (v1_funct_1 @ X0)
% 0.23/0.56          | ~ (v1_relat_1 @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.56  thf('29', plain, ((v1_relat_1 @ sk_D_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.56  thf('30', plain, ((v1_funct_1 @ sk_D_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('31', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ X0) @ sk_C)
% 0.23/0.56            = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.23/0.56          | ~ (v1_funct_1 @ X0)
% 0.23/0.56          | ~ (v1_relat_1 @ X0))),
% 0.23/0.56      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.23/0.56  thf('32', plain,
% 0.23/0.56      (((k1_funct_1 @ (k5_relat_1 @ sk_D_1 @ sk_E_1) @ sk_C)
% 0.23/0.56         != (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('33', plain,
% 0.23/0.56      ((((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C))
% 0.23/0.56          != (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))
% 0.23/0.56        | ~ (v1_relat_1 @ sk_E_1)
% 0.23/0.56        | ~ (v1_funct_1 @ sk_E_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.56  thf('34', plain, ((v1_relat_1 @ sk_E_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('35', plain, ((v1_funct_1 @ sk_E_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('36', plain,
% 0.23/0.56      (((k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C))
% 0.23/0.56         != (k1_funct_1 @ sk_E_1 @ (k1_funct_1 @ sk_D_1 @ sk_C)))),
% 0.23/0.56      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.23/0.56  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.23/0.56  
% 0.23/0.56  % SZS output end Refutation
% 0.23/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
