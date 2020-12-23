%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTcEVP9M0K

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:53 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 290 expanded)
%              Number of leaves         :   33 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  589 (3348 expanded)
%              Number of equality atoms :   39 (  80 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X19 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['20','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','25'])).

thf('27',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['15','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X11: $i] :
      ( ( ( k2_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('50',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['32','47','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTcEVP9M0K
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 195 iterations in 0.271s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.72  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.54/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.72  thf(t4_funct_2, conjecture,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.72       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.72         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.72           ( m1_subset_1 @
% 0.54/0.72             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.54/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.72    (~( ![A:$i,B:$i]:
% 0.54/0.72        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.72          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.72            ( ( v1_funct_1 @ B ) & 
% 0.54/0.72              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.72              ( m1_subset_1 @
% 0.54/0.72                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.54/0.72    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.54/0.72  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(d10_xboole_0, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.72  thf('1', plain,
% 0.54/0.72      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.72  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.54/0.72      inference('simplify', [status(thm)], ['1'])).
% 0.54/0.72  thf(t11_relset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ C ) =>
% 0.54/0.72       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.54/0.72           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.54/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.54/0.72  thf('3', plain,
% 0.54/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.72         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.54/0.72          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ X19)
% 0.54/0.72          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.54/0.72          | ~ (v1_relat_1 @ X17))),
% 0.54/0.72      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.54/0.72  thf('4', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         (~ (v1_relat_1 @ X0)
% 0.54/0.72          | (m1_subset_1 @ X0 @ 
% 0.54/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.54/0.72          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.72  thf('5', plain,
% 0.54/0.72      (((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.54/0.72        | ~ (v1_relat_1 @ sk_B_1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['0', '4'])).
% 0.54/0.72  thf('6', plain, ((v1_relat_1 @ sk_B_1)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('7', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.72  thf(d1_funct_2, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.72  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.72  thf(zf_stmt_2, axiom,
% 0.54/0.72    (![C:$i,B:$i,A:$i]:
% 0.54/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.72  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.54/0.72  thf(zf_stmt_4, axiom,
% 0.54/0.72    (![B:$i,A:$i]:
% 0.54/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.72  thf(zf_stmt_5, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.54/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.72  thf('8', plain,
% 0.54/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.72         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.54/0.72          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.54/0.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.72  thf('9', plain,
% 0.54/0.72      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.54/0.72        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.72  thf('10', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.72    (![A:$i,B:$i,C:$i]:
% 0.54/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.72  thf('11', plain,
% 0.54/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.72         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.54/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.72  thf('12', plain,
% 0.54/0.72      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.54/0.72         = (k1_relat_1 @ sk_B_1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.72  thf('13', plain,
% 0.54/0.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.72         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 0.54/0.72          | (v1_funct_2 @ X28 @ X26 @ X27)
% 0.54/0.72          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.72  thf('14', plain,
% 0.54/0.72      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.54/0.72        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.54/0.72        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.72  thf('15', plain,
% 0.54/0.72      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.54/0.72        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['14'])).
% 0.54/0.72  thf('16', plain,
% 0.54/0.72      ((~ (v1_funct_1 @ sk_B_1)
% 0.54/0.72        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.54/0.72        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.54/0.72         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.72      inference('split', [status(esa)], ['16'])).
% 0.54/0.72  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('19', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.54/0.72      inference('split', [status(esa)], ['16'])).
% 0.54/0.72  thf('20', plain, (((v1_funct_1 @ sk_B_1))),
% 0.54/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.72  thf('21', plain,
% 0.54/0.72      ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.54/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.72  thf('22', plain,
% 0.54/0.72      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.54/0.72         <= (~
% 0.54/0.72             ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.54/0.72      inference('split', [status(esa)], ['16'])).
% 0.54/0.72  thf('23', plain,
% 0.54/0.72      (((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.72  thf('24', plain,
% 0.54/0.72      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.54/0.72       ~
% 0.54/0.72       ((m1_subset_1 @ sk_B_1 @ 
% 0.54/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.54/0.72       ~ ((v1_funct_1 @ sk_B_1))),
% 0.54/0.72      inference('split', [status(esa)], ['16'])).
% 0.54/0.72  thf('25', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.54/0.72      inference('sat_resolution*', [status(thm)], ['20', '23', '24'])).
% 0.54/0.72  thf('26', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.54/0.72      inference('simpl_trail', [status(thm)], ['17', '25'])).
% 0.54/0.72  thf('27', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.54/0.72      inference('clc', [status(thm)], ['15', '26'])).
% 0.54/0.72  thf('28', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.54/0.72      inference('clc', [status(thm)], ['9', '27'])).
% 0.54/0.72  thf('29', plain,
% 0.54/0.72      (![X24 : $i, X25 : $i]:
% 0.54/0.72         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.72  thf('30', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.54/0.72      inference('clc', [status(thm)], ['9', '27'])).
% 0.54/0.72  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.72  thf('32', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B_1))),
% 0.54/0.72      inference('demod', [status(thm)], ['28', '31'])).
% 0.54/0.72  thf(t29_mcart_1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.72          ( ![B:$i]:
% 0.54/0.72            ( ~( ( r2_hidden @ B @ A ) & 
% 0.54/0.72                 ( ![C:$i,D:$i,E:$i]:
% 0.54/0.72                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.54/0.72                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.72  thf('33', plain,
% 0.54/0.72      (![X20 : $i]:
% 0.54/0.72         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 0.54/0.72      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.54/0.72  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(d3_tarski, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.72  thf('35', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.72          | (r2_hidden @ X0 @ X2)
% 0.54/0.72          | ~ (r1_tarski @ X1 @ X2))),
% 0.54/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.72  thf('36', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.72  thf('37', plain,
% 0.54/0.72      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.54/0.72        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ sk_A))),
% 0.54/0.72      inference('sup-', [status(thm)], ['33', '36'])).
% 0.54/0.72  thf(t7_ordinal1, axiom,
% 0.54/0.72    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.72  thf('38', plain,
% 0.54/0.72      (![X12 : $i, X13 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.54/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.72  thf('39', plain,
% 0.54/0.72      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.54/0.72        | ~ (r1_tarski @ sk_A @ (sk_B @ (k2_relat_1 @ sk_B_1))))),
% 0.54/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.72  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.72  thf('41', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.54/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.72  thf('42', plain, (((k2_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.54/0.72  thf(t65_relat_1, axiom,
% 0.54/0.72    (![A:$i]:
% 0.54/0.72     ( ( v1_relat_1 @ A ) =>
% 0.54/0.72       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.72         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.72  thf('43', plain,
% 0.54/0.72      (![X11 : $i]:
% 0.54/0.72         (((k2_relat_1 @ X11) != (k1_xboole_0))
% 0.54/0.72          | ((k1_relat_1 @ X11) = (k1_xboole_0))
% 0.54/0.72          | ~ (v1_relat_1 @ X11))),
% 0.54/0.72      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.54/0.72  thf('44', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | ~ (v1_relat_1 @ sk_B_1)
% 0.54/0.72        | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.72  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('46', plain,
% 0.54/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.72        | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['44', '45'])).
% 0.54/0.72  thf('47', plain, (((k1_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 0.54/0.72      inference('simplify', [status(thm)], ['46'])).
% 0.54/0.72  thf('48', plain,
% 0.54/0.72      (![X24 : $i, X25 : $i]:
% 0.54/0.72         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.72  thf('49', plain,
% 0.54/0.72      (![X24 : $i, X25 : $i]:
% 0.54/0.72         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.72  thf('50', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 0.54/0.72      inference('simplify', [status(thm)], ['49'])).
% 0.54/0.72  thf('51', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.54/0.72      inference('sup+', [status(thm)], ['48', '50'])).
% 0.54/0.72  thf('52', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.54/0.72      inference('eq_fact', [status(thm)], ['51'])).
% 0.54/0.72  thf('53', plain, ($false),
% 0.54/0.72      inference('demod', [status(thm)], ['32', '47', '52'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
