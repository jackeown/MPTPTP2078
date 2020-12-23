%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ISWDt0vDQa

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:32 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 823 expanded)
%              Number of leaves         :   52 ( 269 expanded)
%              Depth                    :   18
%              Number of atoms          : 1048 (10084 expanded)
%              Number of equality atoms :  103 ( 722 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X44 )
       != X42 )
      | ~ ( r2_hidden @ X45 @ X42 )
      | ( r2_hidden @ ( k4_tarski @ X45 @ ( sk_E @ X45 @ X44 ) ) @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_C_1 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('36',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34','35','40'])).

thf('42',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k11_relat_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X30 @ ( k1_tarski @ X29 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['42','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k11_relat_1 @ X18 @ X19 )
        = ( k9_relat_1 @ X18 @ ( k1_tarski @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','53','54'])).

thf('56',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('59',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','61'])).

thf('63',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('65',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['19','63','64','65'])).

thf('67',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','69'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('71',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('72',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != ( k1_tarski @ X27 ) )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('74',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('75',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['73','76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('81',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','82'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

thf('87',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('89',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ISWDt0vDQa
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.79/2.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.79/2.00  % Solved by: fo/fo7.sh
% 1.79/2.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.79/2.00  % done 1487 iterations in 1.532s
% 1.79/2.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.79/2.00  % SZS output start Refutation
% 1.79/2.00  thf(sk_B_type, type, sk_B: $i).
% 1.79/2.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.79/2.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.79/2.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.79/2.00  thf(sk_A_type, type, sk_A: $i).
% 1.79/2.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.79/2.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.79/2.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.79/2.00  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 1.79/2.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.79/2.00  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.79/2.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.79/2.00  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.79/2.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.79/2.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.79/2.00  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.79/2.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.79/2.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.79/2.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.79/2.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.79/2.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.79/2.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.79/2.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.79/2.00  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.79/2.00  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.79/2.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.79/2.00  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.79/2.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.79/2.00  thf(d3_tarski, axiom,
% 1.79/2.00    (![A:$i,B:$i]:
% 1.79/2.00     ( ( r1_tarski @ A @ B ) <=>
% 1.79/2.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.79/2.00  thf('0', plain,
% 1.79/2.00      (![X1 : $i, X3 : $i]:
% 1.79/2.00         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.79/2.00      inference('cnf', [status(esa)], [d3_tarski])).
% 1.79/2.00  thf(t62_funct_2, conjecture,
% 1.79/2.00    (![A:$i,B:$i,C:$i]:
% 1.79/2.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.79/2.00         ( m1_subset_1 @
% 1.79/2.00           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.79/2.00       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.79/2.00         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.79/2.00           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.79/2.00  thf(zf_stmt_0, negated_conjecture,
% 1.79/2.00    (~( ![A:$i,B:$i,C:$i]:
% 1.79/2.00        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.79/2.00            ( m1_subset_1 @
% 1.79/2.00              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.79/2.00          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.79/2.00            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.79/2.00              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 1.79/2.00    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 1.79/2.00  thf('1', plain,
% 1.79/2.00      ((m1_subset_1 @ sk_C_1 @ 
% 1.79/2.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf(t22_relset_1, axiom,
% 1.79/2.00    (![A:$i,B:$i,C:$i]:
% 1.79/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.79/2.00       ( ( ![D:$i]:
% 1.79/2.00           ( ~( ( r2_hidden @ D @ B ) & 
% 1.79/2.00                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 1.79/2.00         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 1.79/2.00  thf('2', plain,
% 1.79/2.00      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.79/2.00         (((k1_relset_1 @ X42 @ X43 @ X44) != (X42))
% 1.79/2.00          | ~ (r2_hidden @ X45 @ X42)
% 1.79/2.00          | (r2_hidden @ (k4_tarski @ X45 @ (sk_E @ X45 @ X44)) @ X44)
% 1.79/2.00          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 1.79/2.00      inference('cnf', [status(esa)], [t22_relset_1])).
% 1.79/2.00  thf('3', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1)
% 1.79/2.00          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.79/2.00          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 1.79/2.00              != (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('sup-', [status(thm)], ['1', '2'])).
% 1.79/2.00  thf('4', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf(d1_funct_2, axiom,
% 1.79/2.00    (![A:$i,B:$i,C:$i]:
% 1.79/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.79/2.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.79/2.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.79/2.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.79/2.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.79/2.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.79/2.00  thf(zf_stmt_1, axiom,
% 1.79/2.00    (![C:$i,B:$i,A:$i]:
% 1.79/2.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.79/2.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.79/2.00  thf('5', plain,
% 1.79/2.00      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.79/2.00         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 1.79/2.00          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 1.79/2.00          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.79/2.00  thf('6', plain,
% 1.79/2.00      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 1.79/2.00        | ((k1_tarski @ sk_A)
% 1.79/2.00            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 1.79/2.00      inference('sup-', [status(thm)], ['4', '5'])).
% 1.79/2.00  thf(zf_stmt_2, axiom,
% 1.79/2.00    (![B:$i,A:$i]:
% 1.79/2.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.79/2.00       ( zip_tseitin_0 @ B @ A ) ))).
% 1.79/2.00  thf('7', plain,
% 1.79/2.00      (![X47 : $i, X48 : $i]:
% 1.79/2.00         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.79/2.00  thf('8', plain,
% 1.79/2.00      ((m1_subset_1 @ sk_C_1 @ 
% 1.79/2.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.79/2.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.79/2.00  thf(zf_stmt_5, axiom,
% 1.79/2.00    (![A:$i,B:$i,C:$i]:
% 1.79/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.79/2.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.79/2.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.79/2.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.79/2.00  thf('9', plain,
% 1.79/2.00      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.79/2.00         (~ (zip_tseitin_0 @ X52 @ X53)
% 1.79/2.00          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 1.79/2.00          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.79/2.00  thf('10', plain,
% 1.79/2.00      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 1.79/2.00        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('sup-', [status(thm)], ['8', '9'])).
% 1.79/2.00  thf('11', plain,
% 1.79/2.00      ((((sk_B) = (k1_xboole_0))
% 1.79/2.00        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('sup-', [status(thm)], ['7', '10'])).
% 1.79/2.00  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf('13', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 1.79/2.00      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 1.79/2.00  thf('14', plain,
% 1.79/2.00      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))),
% 1.79/2.00      inference('demod', [status(thm)], ['6', '13'])).
% 1.79/2.00  thf('15', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1)
% 1.79/2.00          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.79/2.00          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['3', '14'])).
% 1.79/2.00  thf('16', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.79/2.00          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C_1)) @ sk_C_1))),
% 1.79/2.00      inference('simplify', [status(thm)], ['15'])).
% 1.79/2.00  thf('17', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 1.79/2.00          | (r2_hidden @ 
% 1.79/2.00             (k4_tarski @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ 
% 1.79/2.00              (sk_E @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ sk_C_1)) @ 
% 1.79/2.00             sk_C_1))),
% 1.79/2.00      inference('sup-', [status(thm)], ['0', '16'])).
% 1.79/2.00  thf(t7_ordinal1, axiom,
% 1.79/2.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.79/2.00  thf('18', plain,
% 1.79/2.00      (![X31 : $i, X32 : $i]:
% 1.79/2.00         (~ (r2_hidden @ X31 @ X32) | ~ (r1_tarski @ X32 @ X31))),
% 1.79/2.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.79/2.00  thf('19', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 1.79/2.00          | ~ (r1_tarski @ sk_C_1 @ 
% 1.79/2.00               (k4_tarski @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ 
% 1.79/2.00                (sk_E @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ sk_C_1))))),
% 1.79/2.00      inference('sup-', [status(thm)], ['17', '18'])).
% 1.79/2.00  thf('20', plain,
% 1.79/2.00      ((m1_subset_1 @ sk_C_1 @ 
% 1.79/2.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf(cc2_relset_1, axiom,
% 1.79/2.00    (![A:$i,B:$i,C:$i]:
% 1.79/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.79/2.00  thf('21', plain,
% 1.79/2.00      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.79/2.00         ((v4_relat_1 @ X36 @ X37)
% 1.79/2.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.79/2.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.79/2.00  thf('22', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 1.79/2.00      inference('sup-', [status(thm)], ['20', '21'])).
% 1.79/2.00  thf(t209_relat_1, axiom,
% 1.79/2.00    (![A:$i,B:$i]:
% 1.79/2.00     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.79/2.00       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.79/2.00  thf('23', plain,
% 1.79/2.00      (![X24 : $i, X25 : $i]:
% 1.79/2.00         (((X24) = (k7_relat_1 @ X24 @ X25))
% 1.79/2.00          | ~ (v4_relat_1 @ X24 @ X25)
% 1.79/2.00          | ~ (v1_relat_1 @ X24))),
% 1.79/2.00      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.79/2.00  thf('24', plain,
% 1.79/2.00      ((~ (v1_relat_1 @ sk_C_1)
% 1.79/2.00        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 1.79/2.00      inference('sup-', [status(thm)], ['22', '23'])).
% 1.79/2.00  thf('25', plain,
% 1.79/2.00      ((m1_subset_1 @ sk_C_1 @ 
% 1.79/2.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf(cc1_relset_1, axiom,
% 1.79/2.00    (![A:$i,B:$i,C:$i]:
% 1.79/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.00       ( v1_relat_1 @ C ) ))).
% 1.79/2.00  thf('26', plain,
% 1.79/2.00      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.79/2.00         ((v1_relat_1 @ X33)
% 1.79/2.00          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.79/2.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.79/2.00  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 1.79/2.00      inference('sup-', [status(thm)], ['25', '26'])).
% 1.79/2.00  thf('28', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['24', '27'])).
% 1.79/2.00  thf(t148_relat_1, axiom,
% 1.79/2.00    (![A:$i,B:$i]:
% 1.79/2.00     ( ( v1_relat_1 @ B ) =>
% 1.79/2.00       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.79/2.00  thf('29', plain,
% 1.79/2.00      (![X20 : $i, X21 : $i]:
% 1.79/2.00         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.79/2.00          | ~ (v1_relat_1 @ X20))),
% 1.79/2.00      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.79/2.00  thf(t64_relat_1, axiom,
% 1.79/2.00    (![A:$i]:
% 1.79/2.00     ( ( v1_relat_1 @ A ) =>
% 1.79/2.00       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.79/2.00           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.79/2.00         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.79/2.00  thf('30', plain,
% 1.79/2.00      (![X26 : $i]:
% 1.79/2.00         (((k2_relat_1 @ X26) != (k1_xboole_0))
% 1.79/2.00          | ((X26) = (k1_xboole_0))
% 1.79/2.00          | ~ (v1_relat_1 @ X26))),
% 1.79/2.00      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.79/2.00  thf('31', plain,
% 1.79/2.00      (![X0 : $i, X1 : $i]:
% 1.79/2.00         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 1.79/2.00          | ~ (v1_relat_1 @ X1)
% 1.79/2.00          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.79/2.00          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 1.79/2.00      inference('sup-', [status(thm)], ['29', '30'])).
% 1.79/2.00  thf('32', plain,
% 1.79/2.00      ((~ (v1_relat_1 @ sk_C_1)
% 1.79/2.00        | ((k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 1.79/2.00        | ~ (v1_relat_1 @ sk_C_1)
% 1.79/2.00        | ((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 1.79/2.00      inference('sup-', [status(thm)], ['28', '31'])).
% 1.79/2.00  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 1.79/2.00      inference('sup-', [status(thm)], ['25', '26'])).
% 1.79/2.00  thf('34', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['24', '27'])).
% 1.79/2.00  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 1.79/2.00      inference('sup-', [status(thm)], ['25', '26'])).
% 1.79/2.00  thf('36', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['24', '27'])).
% 1.79/2.00  thf('37', plain,
% 1.79/2.00      (![X20 : $i, X21 : $i]:
% 1.79/2.00         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.79/2.00          | ~ (v1_relat_1 @ X20))),
% 1.79/2.00      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.79/2.00  thf('38', plain,
% 1.79/2.00      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 1.79/2.00        | ~ (v1_relat_1 @ sk_C_1))),
% 1.79/2.00      inference('sup+', [status(thm)], ['36', '37'])).
% 1.79/2.00  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 1.79/2.00      inference('sup-', [status(thm)], ['25', '26'])).
% 1.79/2.00  thf('40', plain,
% 1.79/2.00      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['38', '39'])).
% 1.79/2.00  thf('41', plain,
% 1.79/2.00      ((((sk_C_1) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C_1) != (k1_xboole_0)))),
% 1.79/2.00      inference('demod', [status(thm)], ['32', '33', '34', '35', '40'])).
% 1.79/2.00  thf('42', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['24', '27'])).
% 1.79/2.00  thf(t205_relat_1, axiom,
% 1.79/2.00    (![A:$i,B:$i]:
% 1.79/2.00     ( ( v1_relat_1 @ B ) =>
% 1.79/2.00       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 1.79/2.00         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 1.79/2.00  thf('43', plain,
% 1.79/2.00      (![X22 : $i, X23 : $i]:
% 1.79/2.00         (((k11_relat_1 @ X22 @ X23) = (k1_xboole_0))
% 1.79/2.00          | (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 1.79/2.00          | ~ (v1_relat_1 @ X22))),
% 1.79/2.00      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.79/2.00  thf(t168_funct_1, axiom,
% 1.79/2.00    (![A:$i,B:$i]:
% 1.79/2.00     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.79/2.00       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.79/2.00         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 1.79/2.00           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.79/2.00  thf('44', plain,
% 1.79/2.00      (![X29 : $i, X30 : $i]:
% 1.79/2.00         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 1.79/2.00          | ((k2_relat_1 @ (k7_relat_1 @ X30 @ (k1_tarski @ X29)))
% 1.79/2.00              = (k1_tarski @ (k1_funct_1 @ X30 @ X29)))
% 1.79/2.00          | ~ (v1_funct_1 @ X30)
% 1.79/2.00          | ~ (v1_relat_1 @ X30))),
% 1.79/2.00      inference('cnf', [status(esa)], [t168_funct_1])).
% 1.79/2.00  thf('45', plain,
% 1.79/2.00      (![X0 : $i, X1 : $i]:
% 1.79/2.00         (~ (v1_relat_1 @ X0)
% 1.79/2.00          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.79/2.00          | ~ (v1_relat_1 @ X0)
% 1.79/2.00          | ~ (v1_funct_1 @ X0)
% 1.79/2.00          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_tarski @ X1)))
% 1.79/2.00              = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 1.79/2.00      inference('sup-', [status(thm)], ['43', '44'])).
% 1.79/2.00  thf('46', plain,
% 1.79/2.00      (![X0 : $i, X1 : $i]:
% 1.79/2.00         (((k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_tarski @ X1)))
% 1.79/2.00            = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 1.79/2.00          | ~ (v1_funct_1 @ X0)
% 1.79/2.00          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.79/2.00          | ~ (v1_relat_1 @ X0))),
% 1.79/2.00      inference('simplify', [status(thm)], ['45'])).
% 1.79/2.00  thf('47', plain,
% 1.79/2.00      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 1.79/2.00        | ~ (v1_relat_1 @ sk_C_1)
% 1.79/2.00        | ((k11_relat_1 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 1.79/2.00        | ~ (v1_funct_1 @ sk_C_1))),
% 1.79/2.00      inference('sup+', [status(thm)], ['42', '46'])).
% 1.79/2.00  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 1.79/2.00      inference('sup-', [status(thm)], ['25', '26'])).
% 1.79/2.00  thf(d16_relat_1, axiom,
% 1.79/2.00    (![A:$i]:
% 1.79/2.00     ( ( v1_relat_1 @ A ) =>
% 1.79/2.00       ( ![B:$i]:
% 1.79/2.00         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.79/2.00  thf('49', plain,
% 1.79/2.00      (![X18 : $i, X19 : $i]:
% 1.79/2.00         (((k11_relat_1 @ X18 @ X19) = (k9_relat_1 @ X18 @ (k1_tarski @ X19)))
% 1.79/2.00          | ~ (v1_relat_1 @ X18))),
% 1.79/2.00      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.79/2.00  thf('50', plain,
% 1.79/2.00      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['38', '39'])).
% 1.79/2.00  thf('51', plain,
% 1.79/2.00      ((((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))
% 1.79/2.00        | ~ (v1_relat_1 @ sk_C_1))),
% 1.79/2.00      inference('sup+', [status(thm)], ['49', '50'])).
% 1.79/2.00  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 1.79/2.00      inference('sup-', [status(thm)], ['25', '26'])).
% 1.79/2.00  thf('53', plain, (((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))),
% 1.79/2.00      inference('demod', [status(thm)], ['51', '52'])).
% 1.79/2.00  thf('54', plain, ((v1_funct_1 @ sk_C_1)),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf('55', plain,
% 1.79/2.00      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 1.79/2.00        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.79/2.00      inference('demod', [status(thm)], ['47', '48', '53', '54'])).
% 1.79/2.00  thf('56', plain,
% 1.79/2.00      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 1.79/2.00         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf('57', plain,
% 1.79/2.00      ((m1_subset_1 @ sk_C_1 @ 
% 1.79/2.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf(redefinition_k2_relset_1, axiom,
% 1.79/2.00    (![A:$i,B:$i,C:$i]:
% 1.79/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.79/2.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.79/2.00  thf('58', plain,
% 1.79/2.00      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.79/2.00         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 1.79/2.00          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 1.79/2.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.79/2.00  thf('59', plain,
% 1.79/2.00      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 1.79/2.00         = (k2_relat_1 @ sk_C_1))),
% 1.79/2.00      inference('sup-', [status(thm)], ['57', '58'])).
% 1.79/2.00  thf('60', plain,
% 1.79/2.00      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['56', '59'])).
% 1.79/2.00  thf('61', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 1.79/2.00      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 1.79/2.00  thf('62', plain,
% 1.79/2.00      ((((sk_C_1) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.79/2.00      inference('demod', [status(thm)], ['41', '61'])).
% 1.79/2.00  thf('63', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.79/2.00      inference('simplify', [status(thm)], ['62'])).
% 1.79/2.00  thf('64', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.79/2.00      inference('simplify', [status(thm)], ['62'])).
% 1.79/2.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.79/2.00  thf('65', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.79/2.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.79/2.00  thf('66', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 1.79/2.00      inference('demod', [status(thm)], ['19', '63', '64', '65'])).
% 1.79/2.00  thf('67', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.79/2.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.79/2.00  thf(d10_xboole_0, axiom,
% 1.79/2.00    (![A:$i,B:$i]:
% 1.79/2.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.79/2.00  thf('68', plain,
% 1.79/2.00      (![X4 : $i, X6 : $i]:
% 1.79/2.00         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.79/2.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.79/2.00  thf('69', plain,
% 1.79/2.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.79/2.00      inference('sup-', [status(thm)], ['67', '68'])).
% 1.79/2.00  thf('70', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.79/2.00      inference('sup-', [status(thm)], ['66', '69'])).
% 1.79/2.00  thf(t60_relat_1, axiom,
% 1.79/2.00    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.79/2.00     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.79/2.00  thf('71', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.79/2.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.79/2.00  thf(t14_funct_1, axiom,
% 1.79/2.00    (![A:$i,B:$i]:
% 1.79/2.00     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.79/2.00       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.79/2.00         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.79/2.00  thf('72', plain,
% 1.79/2.00      (![X27 : $i, X28 : $i]:
% 1.79/2.00         (((k1_relat_1 @ X28) != (k1_tarski @ X27))
% 1.79/2.00          | ((k2_relat_1 @ X28) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 1.79/2.00          | ~ (v1_funct_1 @ X28)
% 1.79/2.00          | ~ (v1_relat_1 @ X28))),
% 1.79/2.00      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.79/2.00  thf('73', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         (((k1_xboole_0) != (k1_tarski @ X0))
% 1.79/2.00          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.79/2.00          | ~ (v1_funct_1 @ k1_xboole_0)
% 1.79/2.00          | ((k2_relat_1 @ k1_xboole_0)
% 1.79/2.00              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 1.79/2.00      inference('sup-', [status(thm)], ['71', '72'])).
% 1.79/2.00  thf(t4_subset_1, axiom,
% 1.79/2.00    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.79/2.00  thf('74', plain,
% 1.79/2.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 1.79/2.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.79/2.00  thf('75', plain,
% 1.79/2.00      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.79/2.00         ((v1_relat_1 @ X33)
% 1.79/2.00          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.79/2.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.79/2.00  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.79/2.00      inference('sup-', [status(thm)], ['74', '75'])).
% 1.79/2.00  thf('77', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.79/2.00      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.79/2.00  thf('78', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         (((k1_xboole_0) != (k1_tarski @ X0))
% 1.79/2.00          | ~ (v1_funct_1 @ k1_xboole_0)
% 1.79/2.00          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 1.79/2.00      inference('demod', [status(thm)], ['73', '76', '77'])).
% 1.79/2.00  thf('79', plain, ((v1_funct_1 @ sk_C_1)),
% 1.79/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.79/2.00  thf('80', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.79/2.00      inference('simplify', [status(thm)], ['62'])).
% 1.79/2.00  thf('81', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.79/2.00      inference('demod', [status(thm)], ['79', '80'])).
% 1.79/2.00  thf('82', plain,
% 1.79/2.00      (![X0 : $i]:
% 1.79/2.00         (((k1_xboole_0) != (k1_tarski @ X0))
% 1.79/2.00          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 1.79/2.00      inference('demod', [status(thm)], ['78', '81'])).
% 1.79/2.00  thf('83', plain,
% 1.79/2.00      ((((k1_xboole_0) != (k1_xboole_0))
% 1.79/2.00        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 1.79/2.00      inference('sup-', [status(thm)], ['70', '82'])).
% 1.79/2.00  thf('84', plain,
% 1.79/2.00      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 1.79/2.00      inference('simplify', [status(thm)], ['83'])).
% 1.79/2.00  thf('85', plain,
% 1.79/2.00      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['56', '59'])).
% 1.79/2.00  thf('86', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 1.79/2.00      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 1.79/2.00  thf('87', plain,
% 1.79/2.00      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['85', '86'])).
% 1.79/2.00  thf('88', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.79/2.00      inference('simplify', [status(thm)], ['62'])).
% 1.79/2.00  thf('89', plain,
% 1.79/2.00      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 1.79/2.00      inference('demod', [status(thm)], ['87', '88'])).
% 1.79/2.00  thf('90', plain, ($false),
% 1.79/2.00      inference('simplify_reflect-', [status(thm)], ['84', '89'])).
% 1.79/2.00  
% 1.79/2.00  % SZS output end Refutation
% 1.79/2.00  
% 1.79/2.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
