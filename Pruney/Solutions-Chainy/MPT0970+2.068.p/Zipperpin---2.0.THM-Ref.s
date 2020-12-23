%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A2CyV5peHm

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:26 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 178 expanded)
%              Number of leaves         :   37 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  648 (2355 expanded)
%              Number of equality atoms :   43 ( 164 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( sk_D @ X24 @ X22 ) @ X22 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X24 )
        = X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('6',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('11',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X37 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','28','31'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( X10
       != ( k1_funct_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','41'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['14','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('45',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( X37
        = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( sk_D @ sk_C @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_D @ X24 @ X22 ) ) @ X24 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X24 )
        = X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['3','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['2','50'])).

thf('52',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A2CyV5peHm
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 173 iterations in 0.168s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.38/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.62  thf(t16_funct_2, conjecture,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.62       ( ( ![D:$i]:
% 0.38/0.62           ( ~( ( r2_hidden @ D @ B ) & 
% 0.38/0.62                ( ![E:$i]:
% 0.38/0.62                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.38/0.62                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.38/0.62         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.62          ( ( ![D:$i]:
% 0.38/0.62              ( ~( ( r2_hidden @ D @ B ) & 
% 0.38/0.62                   ( ![E:$i]:
% 0.38/0.62                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.38/0.62                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.38/0.62            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.62         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.38/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.62  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t23_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( ![D:$i]:
% 0.38/0.62           ( ~( ( r2_hidden @ D @ B ) & 
% 0.38/0.62                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.38/0.62         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.62         ((r2_hidden @ (sk_D @ X24 @ X22) @ X22)
% 0.38/0.62          | ((k2_relset_1 @ X23 @ X22 @ X24) = (X22))
% 0.38/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.38/0.62      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.38/0.62        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      ((((k2_relat_1 @ sk_C) = (sk_B))
% 0.38/0.62        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf('11', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.62  thf('12', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X37 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X37 @ sk_B) | (r2_hidden @ (sk_E_1 @ X37) @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('14', plain, ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d1_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_1, axiom,
% 0.38/0.62    (![C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.62         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.38/0.62          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.38/0.62          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.63  thf('17', plain,
% 0.38/0.63      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.38/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.63  thf(zf_stmt_2, axiom,
% 0.38/0.63    (![B:$i,A:$i]:
% 0.38/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.63  thf('18', plain,
% 0.38/0.63      (![X27 : $i, X28 : $i]:
% 0.38/0.63         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.63  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.63  thf('20', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.38/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.63  thf('21', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.63  thf(zf_stmt_5, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.63  thf('22', plain,
% 0.38/0.63      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.38/0.63         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.38/0.63          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.38/0.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.63  thf('23', plain,
% 0.38/0.63      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.63  thf('24', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['20', '23'])).
% 0.38/0.63  thf('25', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.38/0.63      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.38/0.63  thf(t7_ordinal1, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.63  thf('26', plain,
% 0.38/0.63      (![X11 : $i, X12 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.63  thf('27', plain, (~ (r1_tarski @ sk_B @ (sk_D @ sk_C @ sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.63  thf('28', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.38/0.63      inference('sup-', [status(thm)], ['24', '27'])).
% 0.38/0.63  thf('29', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.63  thf('30', plain,
% 0.38/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.63         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.38/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.63  thf('31', plain,
% 0.38/0.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.63  thf('32', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.63      inference('demod', [status(thm)], ['17', '28', '31'])).
% 0.38/0.63  thf(t8_funct_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.63       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.63         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.63           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.38/0.63  thf('33', plain,
% 0.38/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.38/0.63          | ((X10) != (k1_funct_1 @ X9 @ X8))
% 0.38/0.63          | (r2_hidden @ (k4_tarski @ X8 @ X10) @ X9)
% 0.38/0.63          | ~ (v1_funct_1 @ X9)
% 0.38/0.63          | ~ (v1_relat_1 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.38/0.63  thf('34', plain,
% 0.38/0.63      (![X8 : $i, X9 : $i]:
% 0.38/0.63         (~ (v1_relat_1 @ X9)
% 0.38/0.63          | ~ (v1_funct_1 @ X9)
% 0.38/0.63          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.38/0.63          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.63  thf('35', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C)
% 0.38/0.63          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63          | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['32', '34'])).
% 0.38/0.63  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('37', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(cc2_relat_1, axiom,
% 0.38/0.63    (![A:$i]:
% 0.38/0.63     ( ( v1_relat_1 @ A ) =>
% 0.38/0.63       ( ![B:$i]:
% 0.38/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.63  thf('38', plain,
% 0.38/0.63      (![X4 : $i, X5 : $i]:
% 0.38/0.63         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.38/0.63          | (v1_relat_1 @ X4)
% 0.38/0.63          | ~ (v1_relat_1 @ X5))),
% 0.38/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.63  thf('39', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.63  thf(fc6_relat_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.63  thf('40', plain,
% 0.38/0.63      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.38/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.63  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.63  thf('42', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.63          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C))),
% 0.38/0.63      inference('demod', [status(thm)], ['35', '36', '41'])).
% 0.38/0.63  thf('43', plain,
% 0.38/0.63      ((r2_hidden @ 
% 0.38/0.63        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ 
% 0.38/0.63         (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)))) @ 
% 0.38/0.63        sk_C)),
% 0.38/0.63      inference('sup-', [status(thm)], ['14', '42'])).
% 0.38/0.63  thf('44', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.38/0.63      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.38/0.63  thf('45', plain,
% 0.38/0.63      (![X37 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X37 @ sk_B)
% 0.38/0.63          | ((X37) = (k1_funct_1 @ sk_C @ (sk_E_1 @ X37))))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('46', plain,
% 0.38/0.63      (((sk_D @ sk_C @ sk_B)
% 0.38/0.63         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.63  thf('47', plain,
% 0.38/0.63      ((r2_hidden @ 
% 0.38/0.63        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ (sk_D @ sk_C @ sk_B)) @ 
% 0.38/0.63        sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['43', '46'])).
% 0.38/0.63  thf('48', plain,
% 0.38/0.63      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 0.38/0.63         (~ (r2_hidden @ (k4_tarski @ X26 @ (sk_D @ X24 @ X22)) @ X24)
% 0.38/0.63          | ((k2_relset_1 @ X23 @ X22 @ X24) = (X22))
% 0.38/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.38/0.63      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.38/0.63  thf('49', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.38/0.63          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.63  thf('50', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['3', '49'])).
% 0.38/0.63  thf('51', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.38/0.63      inference('sup+', [status(thm)], ['2', '50'])).
% 0.38/0.63  thf('52', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.38/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.63  thf('53', plain, ($false),
% 0.38/0.63      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
