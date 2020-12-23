%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vHzNhAKrfW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:52 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 631 expanded)
%              Number of leaves         :   43 ( 194 expanded)
%              Depth                    :   18
%              Number of atoms          :  925 (7023 expanded)
%              Number of equality atoms :   67 ( 213 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

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
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_4 @ X40 @ X41 )
      | ( zip_tseitin_5 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_4 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_5 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('29',plain,(
    ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_4 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','29'])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','30'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t18_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_relat_1 @ C ) )
           => ~ ( ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( B
                  = ( k1_relat_1 @ C ) ) ) )
        & ~ ( ( B != k1_xboole_0 )
            & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [C: $i] :
      ( ( zip_tseitin_0 @ C )
     => ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( zip_tseitin_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('48',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('49',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ C )
       => ~ ( zip_tseitin_1 @ C @ B @ A ) )
     => ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_2 @ X20 @ X21 @ X22 )
      | ( zip_tseitin_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(zf_stmt_8,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
     => ( ( A = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_11,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B
          = ( k1_relat_1 @ C ) )
        & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) )).

thf(zf_stmt_13,type,(
    zip_tseitin_0: $i > $o )).

thf(zf_stmt_14,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( zip_tseitin_3 @ B @ A )
        & ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_3 @ X25 @ X26 )
      | ~ ( zip_tseitin_2 @ ( sk_C_2 @ X25 @ X26 ) @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( zip_tseitin_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_2 @ X20 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('61',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_3 @ X25 @ X26 )
      | ~ ( zip_tseitin_2 @ ( sk_C_2 @ X25 @ X26 ) @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18
        = ( k1_relat_1 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( zip_tseitin_3 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( sk_C_2 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_2 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ k1_xboole_0 @ X1 ) )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24 != k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('69',plain,(
    ! [X23: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X23 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_2 @ k1_xboole_0 @ X1 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ k1_xboole_0 @ X0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X23: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X23 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X23: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X23 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('78',plain,(
    zip_tseitin_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','78'])).

thf('80',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_5 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_4 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('88',plain,(
    ! [X35: $i] :
      ( zip_tseitin_4 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','78'])).

thf('90',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_4 @ X40 @ X41 )
      | ( zip_tseitin_5 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_4 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['86','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['32','44','45','46','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vHzNhAKrfW
% 0.14/0.38  % Computer   : n023.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 18:30:06 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 267 iterations in 0.248s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.74  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.54/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $o).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.54/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.54/0.74  thf(t4_funct_2, conjecture,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.74         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.74           ( m1_subset_1 @
% 0.54/0.74             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i,B:$i]:
% 0.54/0.74        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.74            ( ( v1_funct_1 @ B ) & 
% 0.54/0.74              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.74              ( m1_subset_1 @
% 0.54/0.74                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      ((~ (v1_funct_1 @ sk_B)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.74        | ~ (m1_subset_1 @ sk_B @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.54/0.74         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('2', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('3', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('4', plain, (((v1_funct_1 @ sk_B))),
% 0.54/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(d10_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('7', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.54/0.74      inference('simplify', [status(thm)], ['6'])).
% 0.54/0.74  thf(t11_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ C ) =>
% 0.54/0.74       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.54/0.74           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.54/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.74         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 0.54/0.74          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.54/0.74          | ~ (v1_relat_1 @ X32))),
% 0.54/0.74      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.54/0.74  thf('9', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | (m1_subset_1 @ X0 @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      (((m1_subset_1 @ sk_B @ 
% 0.54/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.74      inference('sup-', [status(thm)], ['5', '9'])).
% 0.54/0.74  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_B @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      ((~ (m1_subset_1 @ sk_B @ 
% 0.54/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.54/0.74         <= (~
% 0.54/0.74             ((m1_subset_1 @ sk_B @ 
% 0.54/0.74               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      (((m1_subset_1 @ sk_B @ 
% 0.54/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.74  thf('15', plain,
% 0.54/0.74      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.54/0.74       ~
% 0.54/0.74       ((m1_subset_1 @ sk_B @ 
% 0.54/0.74         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.54/0.74       ~ ((v1_funct_1 @ sk_B))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('16', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.74      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.54/0.74  thf('17', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.74      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.54/0.74  thf(d1_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_1, axiom,
% 0.54/0.74    (![B:$i,A:$i]:
% 0.54/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74       ( zip_tseitin_4 @ B @ A ) ))).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      (![X35 : $i, X36 : $i]:
% 0.54/0.74         ((zip_tseitin_4 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.74  thf('19', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_B @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_3, axiom,
% 0.54/0.74    (![C:$i,B:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.54/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_5, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.54/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.54/0.74         (~ (zip_tseitin_4 @ X40 @ X41)
% 0.54/0.74          | (zip_tseitin_5 @ X42 @ X40 @ X41)
% 0.54/0.74          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (((zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.54/0.74        | ~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.74  thf('22', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_B @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.74  thf('23', plain,
% 0.54/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.54/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.74  thf('24', plain,
% 0.54/0.74      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.54/0.74      inference('sup-', [status(thm)], ['22', '23'])).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.74         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.54/0.74          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.54/0.74          | ~ (zip_tseitin_5 @ X39 @ X38 @ X37))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.74  thf('26', plain,
% 0.54/0.74      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.54/0.74        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.54/0.74        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.74  thf('27', plain,
% 0.54/0.74      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.74        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['26'])).
% 0.54/0.74  thf('28', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.74      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.54/0.74  thf('29', plain, (~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.54/0.74      inference('clc', [status(thm)], ['27', '28'])).
% 0.54/0.74  thf('30', plain, (~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.54/0.74      inference('clc', [status(thm)], ['21', '29'])).
% 0.54/0.74  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['18', '30'])).
% 0.54/0.74  thf('32', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ k1_xboole_0)),
% 0.54/0.74      inference('demod', [status(thm)], ['17', '31'])).
% 0.54/0.74  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X4 : $i, X6 : $i]:
% 0.54/0.74         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.54/0.74        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.74  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['18', '30'])).
% 0.54/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.74  thf('37', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['18', '30'])).
% 0.54/0.74  thf('39', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.54/0.74      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.54/0.74  thf(t64_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ A ) =>
% 0.54/0.74       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      (![X8 : $i]:
% 0.54/0.74         (((k2_relat_1 @ X8) != (k1_xboole_0))
% 0.54/0.74          | ((X8) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_relat_1 @ X8))),
% 0.54/0.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_B)
% 0.54/0.74        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.74  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('43', plain,
% 0.54/0.74      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.54/0.74  thf('44', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.54/0.74  thf('45', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.54/0.74  thf(t60_relat_1, axiom,
% 0.54/0.74    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.54/0.74     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.74  thf('46', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.74  thf(t18_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ~( ( ![C:$i]:
% 0.54/0.74            ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.54/0.74              ( ~( ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.54/0.74                   ( ( B ) = ( k1_relat_1 @ C ) ) ) ) ) ) & 
% 0.54/0.74          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_6, axiom,
% 0.54/0.74    (![C:$i]:
% 0.54/0.74     ( ( zip_tseitin_0 @ C ) => ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) ))).
% 0.54/0.74  thf('47', plain,
% 0.54/0.74      (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (zip_tseitin_0 @ X16))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.54/0.74  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.74         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 0.54/0.74          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.54/0.74          | ~ (v1_relat_1 @ X32))),
% 0.54/0.74      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.54/0.74  thf('50', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.74          | (m1_subset_1 @ k1_xboole_0 @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.74  thf('51', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.74  thf('53', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf('54', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.74          | (m1_subset_1 @ k1_xboole_0 @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.54/0.74  thf('55', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (~ (zip_tseitin_0 @ k1_xboole_0)
% 0.54/0.74          | (m1_subset_1 @ k1_xboole_0 @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['47', '54'])).
% 0.54/0.74  thf(zf_stmt_7, axiom,
% 0.54/0.74    (![C:$i,B:$i,A:$i]:
% 0.54/0.74     ( ( ( zip_tseitin_0 @ C ) => ( ~( zip_tseitin_1 @ C @ B @ A ) ) ) =>
% 0.54/0.74       ( zip_tseitin_2 @ C @ B @ A ) ))).
% 0.54/0.74  thf('56', plain,
% 0.54/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.74         ((zip_tseitin_2 @ X20 @ X21 @ X22) | (zip_tseitin_0 @ X20))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.54/0.74  thf(zf_stmt_8, type, zip_tseitin_3 : $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_9, axiom,
% 0.54/0.74    (![B:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_3 @ B @ A ) =>
% 0.54/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_10, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_11, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_12, axiom,
% 0.54/0.74    (![C:$i,B:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.74       ( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.54/0.74         ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ))).
% 0.54/0.74  thf(zf_stmt_13, type, zip_tseitin_0 : $i > $o).
% 0.54/0.74  thf(zf_stmt_14, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ~( ( ~( zip_tseitin_3 @ B @ A ) ) & 
% 0.54/0.74          ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.54/0.74  thf('57', plain,
% 0.54/0.74      (![X25 : $i, X26 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ X25 @ X26)
% 0.54/0.74          | ~ (zip_tseitin_2 @ (sk_C_2 @ X25 @ X26) @ X25 @ X26))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.54/0.74  thf('58', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ (sk_C_2 @ X1 @ X0)) | (zip_tseitin_3 @ X1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.74  thf('59', plain,
% 0.54/0.74      (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (zip_tseitin_0 @ X16))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.54/0.74  thf('60', plain,
% 0.54/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.74         ((zip_tseitin_2 @ X20 @ X21 @ X22) | (zip_tseitin_1 @ X20 @ X21 @ X22))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.54/0.74  thf('61', plain,
% 0.54/0.74      (![X25 : $i, X26 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ X25 @ X26)
% 0.54/0.74          | ~ (zip_tseitin_2 @ (sk_C_2 @ X25 @ X26) @ X25 @ X26))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.54/0.74  thf('62', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_1 @ (sk_C_2 @ X1 @ X0) @ X1 @ X0)
% 0.54/0.74          | (zip_tseitin_3 @ X1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.74  thf('63', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.74         (((X18) = (k1_relat_1 @ X17)) | ~ (zip_tseitin_1 @ X17 @ X18 @ X19))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.54/0.74  thf('64', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ X1 @ X0)
% 0.54/0.74          | ((X1) = (k1_relat_1 @ (sk_C_2 @ X1 @ X0))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.74  thf('65', plain,
% 0.54/0.74      (![X8 : $i]:
% 0.54/0.74         (((k1_relat_1 @ X8) != (k1_xboole_0))
% 0.54/0.74          | ((X8) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_relat_1 @ X8))),
% 0.54/0.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.74  thf('66', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((X0) != (k1_xboole_0))
% 0.54/0.74          | (zip_tseitin_3 @ X0 @ X1)
% 0.54/0.74          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.54/0.74          | ((sk_C_2 @ X0 @ X1) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.74  thf('67', plain,
% 0.54/0.74      (![X1 : $i]:
% 0.54/0.74         (((sk_C_2 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_relat_1 @ (sk_C_2 @ k1_xboole_0 @ X1))
% 0.54/0.74          | (zip_tseitin_3 @ k1_xboole_0 @ X1))),
% 0.54/0.74      inference('simplify', [status(thm)], ['66'])).
% 0.54/0.74  thf('68', plain,
% 0.54/0.74      (![X23 : $i, X24 : $i]:
% 0.54/0.74         (((X24) != (k1_xboole_0)) | ~ (zip_tseitin_3 @ X24 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.54/0.74  thf('69', plain, (![X23 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X23)),
% 0.54/0.74      inference('simplify', [status(thm)], ['68'])).
% 0.54/0.74  thf('70', plain,
% 0.54/0.74      (![X1 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ (sk_C_2 @ k1_xboole_0 @ X1))
% 0.54/0.74          | ((sk_C_2 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.54/0.74      inference('clc', [status(thm)], ['67', '69'])).
% 0.54/0.74  thf('71', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (zip_tseitin_0 @ (sk_C_2 @ k1_xboole_0 @ X0))
% 0.54/0.74          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['59', '70'])).
% 0.54/0.74  thf('72', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ k1_xboole_0 @ X0)
% 0.54/0.74          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['58', '71'])).
% 0.54/0.74  thf('73', plain, (![X23 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X23)),
% 0.54/0.74      inference('simplify', [status(thm)], ['68'])).
% 0.54/0.74  thf('74', plain, (![X0 : $i]: ((sk_C_2 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.74      inference('clc', [status(thm)], ['72', '73'])).
% 0.54/0.74  thf('75', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ (sk_C_2 @ X1 @ X0)) | (zip_tseitin_3 @ X1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.74  thf('76', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ k1_xboole_0) | (zip_tseitin_3 @ k1_xboole_0 @ X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['74', '75'])).
% 0.54/0.74  thf('77', plain, (![X23 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X23)),
% 0.54/0.74      inference('simplify', [status(thm)], ['68'])).
% 0.54/0.74  thf('78', plain, ((zip_tseitin_0 @ k1_xboole_0)),
% 0.54/0.74      inference('clc', [status(thm)], ['76', '77'])).
% 0.54/0.74  thf('79', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['55', '78'])).
% 0.54/0.74  thf('80', plain,
% 0.54/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.54/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.74  thf('81', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['79', '80'])).
% 0.54/0.74  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.74  thf('83', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['81', '82'])).
% 0.54/0.74  thf('84', plain,
% 0.54/0.74      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.74         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.54/0.74          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.54/0.74          | ~ (zip_tseitin_5 @ X39 @ X38 @ X37))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.74  thf('85', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (((X1) != (k1_xboole_0))
% 0.54/0.74          | ~ (zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1)
% 0.54/0.74          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['83', '84'])).
% 0.54/0.74  thf('86', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.74          | ~ (zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['85'])).
% 0.54/0.74  thf('87', plain,
% 0.54/0.74      (![X35 : $i, X36 : $i]:
% 0.54/0.74         ((zip_tseitin_4 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.74  thf('88', plain, (![X35 : $i]: (zip_tseitin_4 @ X35 @ k1_xboole_0)),
% 0.54/0.74      inference('simplify', [status(thm)], ['87'])).
% 0.54/0.74  thf('89', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['55', '78'])).
% 0.54/0.74  thf('90', plain,
% 0.54/0.74      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.54/0.74         (~ (zip_tseitin_4 @ X40 @ X41)
% 0.54/0.74          | (zip_tseitin_5 @ X42 @ X40 @ X41)
% 0.54/0.74          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.74  thf('91', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_4 @ X0 @ X1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['89', '90'])).
% 0.54/0.74  thf('92', plain,
% 0.54/0.74      (![X0 : $i]: (zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['88', '91'])).
% 0.54/0.74  thf('93', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.74      inference('demod', [status(thm)], ['86', '92'])).
% 0.54/0.74  thf('94', plain, ($false),
% 0.54/0.74      inference('demod', [status(thm)], ['32', '44', '45', '46', '93'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
