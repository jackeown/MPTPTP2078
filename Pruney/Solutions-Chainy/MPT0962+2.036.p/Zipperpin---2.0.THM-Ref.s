%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TYoGJicu63

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:54 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 220 expanded)
%              Number of leaves         :   39 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  728 (2215 expanded)
%              Number of equality atoms :   43 (  65 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( sk_C @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( v1_funct_2 @ ( sk_C @ X31 @ X32 ) @ X32 @ X31 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

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

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_funct_2 @ sk_B_1 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('31',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X17 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['28','42'])).

thf('44',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

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

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('59',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','40','41'])).

thf('60',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['57','60'])).

thf('62',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','61'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','63','65','66'])).

thf('68',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['43','68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TYoGJicu63
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.34/1.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.34/1.52  % Solved by: fo/fo7.sh
% 1.34/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.34/1.52  % done 914 iterations in 1.069s
% 1.34/1.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.34/1.52  % SZS output start Refutation
% 1.34/1.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.34/1.52  thf(sk_B_type, type, sk_B: $i > $i).
% 1.34/1.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.34/1.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.34/1.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.34/1.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.34/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.34/1.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.34/1.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.34/1.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.34/1.52  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.34/1.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.34/1.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.34/1.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.34/1.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.34/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.34/1.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.34/1.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.34/1.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.34/1.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.34/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.34/1.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.34/1.52  thf(t34_mcart_1, axiom,
% 1.34/1.52    (![A:$i]:
% 1.34/1.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.34/1.52          ( ![B:$i]:
% 1.34/1.52            ( ~( ( r2_hidden @ B @ A ) & 
% 1.34/1.52                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 1.34/1.52                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.34/1.52                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 1.34/1.52  thf('0', plain,
% 1.34/1.52      (![X18 : $i]:
% 1.34/1.52         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 1.34/1.52      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.34/1.52  thf(d10_xboole_0, axiom,
% 1.34/1.52    (![A:$i,B:$i]:
% 1.34/1.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.34/1.52  thf('1', plain,
% 1.34/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.34/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.34/1.52  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.34/1.52      inference('simplify', [status(thm)], ['1'])).
% 1.34/1.52  thf(t3_subset, axiom,
% 1.34/1.52    (![A:$i,B:$i]:
% 1.34/1.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.34/1.52  thf('3', plain,
% 1.34/1.52      (![X6 : $i, X8 : $i]:
% 1.34/1.52         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.34/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.34/1.52  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.34/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.34/1.52  thf(t5_subset, axiom,
% 1.34/1.52    (![A:$i,B:$i,C:$i]:
% 1.34/1.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.34/1.52          ( v1_xboole_0 @ C ) ) ))).
% 1.34/1.52  thf('5', plain,
% 1.34/1.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.34/1.52         (~ (r2_hidden @ X9 @ X10)
% 1.34/1.52          | ~ (v1_xboole_0 @ X11)
% 1.34/1.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.34/1.52      inference('cnf', [status(esa)], [t5_subset])).
% 1.34/1.52  thf('6', plain,
% 1.34/1.52      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.34/1.52      inference('sup-', [status(thm)], ['4', '5'])).
% 1.34/1.52  thf('7', plain,
% 1.34/1.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.34/1.52      inference('sup-', [status(thm)], ['0', '6'])).
% 1.34/1.52  thf('8', plain,
% 1.34/1.52      (![X18 : $i]:
% 1.34/1.52         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 1.34/1.52      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.34/1.52  thf(t113_zfmisc_1, axiom,
% 1.34/1.52    (![A:$i,B:$i]:
% 1.34/1.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.34/1.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.34/1.52  thf('9', plain,
% 1.34/1.52      (![X4 : $i, X5 : $i]:
% 1.34/1.52         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.34/1.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.34/1.52  thf('10', plain,
% 1.34/1.52      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.34/1.52      inference('simplify', [status(thm)], ['9'])).
% 1.34/1.52  thf(rc1_funct_2, axiom,
% 1.34/1.52    (![A:$i,B:$i]:
% 1.34/1.52     ( ?[C:$i]:
% 1.34/1.52       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 1.34/1.52         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 1.34/1.52         ( v1_relat_1 @ C ) & 
% 1.34/1.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.34/1.52  thf('11', plain,
% 1.34/1.52      (![X31 : $i, X32 : $i]:
% 1.34/1.52         (m1_subset_1 @ (sk_C @ X31 @ X32) @ 
% 1.34/1.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))),
% 1.34/1.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 1.34/1.52  thf('12', plain,
% 1.34/1.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.34/1.52         (~ (r2_hidden @ X9 @ X10)
% 1.34/1.52          | ~ (v1_xboole_0 @ X11)
% 1.34/1.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.34/1.52      inference('cnf', [status(esa)], [t5_subset])).
% 1.34/1.52  thf('13', plain,
% 1.34/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.34/1.52          | ~ (r2_hidden @ X2 @ (sk_C @ X0 @ X1)))),
% 1.34/1.52      inference('sup-', [status(thm)], ['11', '12'])).
% 1.34/1.52  thf('14', plain,
% 1.34/1.52      (![X0 : $i, X1 : $i]:
% 1.34/1.52         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.34/1.52          | ~ (r2_hidden @ X1 @ (sk_C @ X0 @ k1_xboole_0)))),
% 1.34/1.52      inference('sup-', [status(thm)], ['10', '13'])).
% 1.34/1.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.34/1.52  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.34/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.34/1.52  thf('16', plain,
% 1.34/1.52      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (sk_C @ X0 @ k1_xboole_0))),
% 1.34/1.52      inference('demod', [status(thm)], ['14', '15'])).
% 1.34/1.52  thf('17', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.34/1.52      inference('sup-', [status(thm)], ['8', '16'])).
% 1.34/1.52  thf('18', plain,
% 1.34/1.52      (![X31 : $i, X32 : $i]: (v1_funct_2 @ (sk_C @ X31 @ X32) @ X32 @ X31)),
% 1.34/1.52      inference('cnf', [status(esa)], [rc1_funct_2])).
% 1.34/1.52  thf('19', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.34/1.52      inference('sup+', [status(thm)], ['17', '18'])).
% 1.34/1.52  thf('20', plain,
% 1.34/1.52      (![X0 : $i, X1 : $i]:
% 1.34/1.52         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.34/1.52      inference('sup+', [status(thm)], ['7', '19'])).
% 1.34/1.52  thf('21', plain,
% 1.34/1.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.34/1.52      inference('sup-', [status(thm)], ['0', '6'])).
% 1.34/1.52  thf(t60_relat_1, axiom,
% 1.34/1.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.34/1.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.34/1.52  thf('22', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.34/1.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.34/1.52  thf('23', plain,
% 1.34/1.52      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.34/1.52      inference('sup+', [status(thm)], ['21', '22'])).
% 1.34/1.52  thf(t4_funct_2, conjecture,
% 1.34/1.52    (![A:$i,B:$i]:
% 1.34/1.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.34/1.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.34/1.52         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.34/1.52           ( m1_subset_1 @
% 1.34/1.52             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.34/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.34/1.52    (~( ![A:$i,B:$i]:
% 1.34/1.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.34/1.52          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.34/1.52            ( ( v1_funct_1 @ B ) & 
% 1.34/1.52              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.34/1.52              ( m1_subset_1 @
% 1.34/1.52                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 1.34/1.52    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 1.34/1.52  thf('24', plain,
% 1.34/1.52      ((~ (v1_funct_1 @ sk_B_1)
% 1.34/1.52        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 1.34/1.52        | ~ (m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 1.34/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.52  thf('25', plain,
% 1.34/1.52      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 1.34/1.52         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('split', [status(esa)], ['24'])).
% 1.34/1.52  thf('26', plain,
% 1.34/1.52      (((~ (v1_funct_2 @ sk_B_1 @ k1_xboole_0 @ sk_A)
% 1.34/1.52         | ~ (v1_xboole_0 @ sk_B_1)))
% 1.34/1.52         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('sup-', [status(thm)], ['23', '25'])).
% 1.34/1.52  thf('27', plain,
% 1.34/1.52      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_B_1)))
% 1.34/1.52         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('sup-', [status(thm)], ['20', '26'])).
% 1.34/1.52  thf('28', plain,
% 1.34/1.52      ((~ (v1_xboole_0 @ sk_B_1))
% 1.34/1.52         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('simplify', [status(thm)], ['27'])).
% 1.34/1.52  thf('29', plain, ((v1_funct_1 @ sk_B_1)),
% 1.34/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.52  thf('30', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 1.34/1.52      inference('split', [status(esa)], ['24'])).
% 1.34/1.52  thf('31', plain, (((v1_funct_1 @ sk_B_1))),
% 1.34/1.52      inference('sup-', [status(thm)], ['29', '30'])).
% 1.34/1.52  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 1.34/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.52  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.34/1.52      inference('simplify', [status(thm)], ['1'])).
% 1.34/1.52  thf(t11_relset_1, axiom,
% 1.34/1.52    (![A:$i,B:$i,C:$i]:
% 1.34/1.52     ( ( v1_relat_1 @ C ) =>
% 1.34/1.52       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.34/1.52           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.34/1.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.34/1.52  thf('34', plain,
% 1.34/1.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.34/1.52         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 1.34/1.52          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ X17)
% 1.34/1.52          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.34/1.52          | ~ (v1_relat_1 @ X15))),
% 1.34/1.52      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.34/1.52  thf('35', plain,
% 1.34/1.52      (![X0 : $i, X1 : $i]:
% 1.34/1.52         (~ (v1_relat_1 @ X0)
% 1.34/1.52          | (m1_subset_1 @ X0 @ 
% 1.34/1.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.34/1.52          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.34/1.52      inference('sup-', [status(thm)], ['33', '34'])).
% 1.34/1.52  thf('36', plain,
% 1.34/1.52      (((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 1.34/1.52        | ~ (v1_relat_1 @ sk_B_1))),
% 1.34/1.52      inference('sup-', [status(thm)], ['32', '35'])).
% 1.34/1.52  thf('37', plain, ((v1_relat_1 @ sk_B_1)),
% 1.34/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.52  thf('38', plain,
% 1.34/1.52      ((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('demod', [status(thm)], ['36', '37'])).
% 1.34/1.52  thf('39', plain,
% 1.34/1.52      ((~ (m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 1.34/1.52         <= (~
% 1.34/1.52             ((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 1.34/1.52      inference('split', [status(esa)], ['24'])).
% 1.34/1.52  thf('40', plain,
% 1.34/1.52      (((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 1.34/1.52      inference('sup-', [status(thm)], ['38', '39'])).
% 1.34/1.52  thf('41', plain,
% 1.34/1.52      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 1.34/1.52       ~
% 1.34/1.52       ((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 1.34/1.52       ~ ((v1_funct_1 @ sk_B_1))),
% 1.34/1.52      inference('split', [status(esa)], ['24'])).
% 1.34/1.52  thf('42', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 1.34/1.52      inference('sat_resolution*', [status(thm)], ['31', '40', '41'])).
% 1.34/1.52  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.34/1.52      inference('simpl_trail', [status(thm)], ['28', '42'])).
% 1.34/1.52  thf('44', plain,
% 1.34/1.52      (![X18 : $i]:
% 1.34/1.52         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 1.34/1.52      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.34/1.52  thf('45', plain,
% 1.34/1.52      ((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('demod', [status(thm)], ['36', '37'])).
% 1.34/1.52  thf('46', plain,
% 1.34/1.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.34/1.52         (~ (r2_hidden @ X9 @ X10)
% 1.34/1.52          | ~ (v1_xboole_0 @ X11)
% 1.34/1.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.34/1.52      inference('cnf', [status(esa)], [t5_subset])).
% 1.34/1.52  thf('47', plain,
% 1.34/1.52      (![X0 : $i]:
% 1.34/1.52         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 1.34/1.52          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.34/1.52      inference('sup-', [status(thm)], ['45', '46'])).
% 1.34/1.52  thf(d1_funct_2, axiom,
% 1.34/1.52    (![A:$i,B:$i,C:$i]:
% 1.34/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.34/1.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.34/1.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.34/1.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.34/1.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.34/1.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.34/1.52  thf(zf_stmt_1, axiom,
% 1.34/1.52    (![B:$i,A:$i]:
% 1.34/1.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.34/1.52       ( zip_tseitin_0 @ B @ A ) ))).
% 1.34/1.52  thf('48', plain,
% 1.34/1.52      (![X23 : $i, X24 : $i]:
% 1.34/1.52         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.34/1.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.34/1.52  thf('49', plain,
% 1.34/1.52      ((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('demod', [status(thm)], ['36', '37'])).
% 1.34/1.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.34/1.52  thf(zf_stmt_3, axiom,
% 1.34/1.52    (![C:$i,B:$i,A:$i]:
% 1.34/1.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.34/1.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.34/1.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.34/1.52  thf(zf_stmt_5, axiom,
% 1.34/1.52    (![A:$i,B:$i,C:$i]:
% 1.34/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.34/1.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.34/1.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.34/1.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.34/1.52  thf('50', plain,
% 1.34/1.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.34/1.52         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.34/1.52          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.34/1.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.34/1.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.34/1.52  thf('51', plain,
% 1.34/1.52      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 1.34/1.52        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 1.34/1.52      inference('sup-', [status(thm)], ['49', '50'])).
% 1.34/1.52  thf('52', plain,
% 1.34/1.52      ((m1_subset_1 @ sk_B_1 @ 
% 1.34/1.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('demod', [status(thm)], ['36', '37'])).
% 1.34/1.52  thf(redefinition_k1_relset_1, axiom,
% 1.34/1.52    (![A:$i,B:$i,C:$i]:
% 1.34/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.34/1.52  thf('53', plain,
% 1.34/1.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.34/1.52         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.34/1.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.34/1.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.34/1.52  thf('54', plain,
% 1.34/1.52      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 1.34/1.52         = (k1_relat_1 @ sk_B_1))),
% 1.34/1.52      inference('sup-', [status(thm)], ['52', '53'])).
% 1.34/1.52  thf('55', plain,
% 1.34/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.34/1.52         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 1.34/1.52          | (v1_funct_2 @ X27 @ X25 @ X26)
% 1.34/1.52          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.34/1.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.34/1.52  thf('56', plain,
% 1.34/1.52      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 1.34/1.52        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 1.34/1.52        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 1.34/1.52      inference('sup-', [status(thm)], ['54', '55'])).
% 1.34/1.52  thf('57', plain,
% 1.34/1.52      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 1.34/1.52        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 1.34/1.52      inference('simplify', [status(thm)], ['56'])).
% 1.34/1.52  thf('58', plain,
% 1.34/1.52      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 1.34/1.52         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 1.34/1.52      inference('split', [status(esa)], ['24'])).
% 1.34/1.52  thf('59', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 1.34/1.52      inference('sat_resolution*', [status(thm)], ['31', '40', '41'])).
% 1.34/1.52  thf('60', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 1.34/1.52      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 1.34/1.52  thf('61', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 1.34/1.52      inference('clc', [status(thm)], ['57', '60'])).
% 1.34/1.52  thf('62', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 1.34/1.52      inference('clc', [status(thm)], ['51', '61'])).
% 1.34/1.52  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 1.34/1.52      inference('sup-', [status(thm)], ['48', '62'])).
% 1.34/1.52  thf('64', plain,
% 1.34/1.52      (![X4 : $i, X5 : $i]:
% 1.34/1.52         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.34/1.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.34/1.52  thf('65', plain,
% 1.34/1.52      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.34/1.52      inference('simplify', [status(thm)], ['64'])).
% 1.34/1.52  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.34/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.34/1.52  thf('67', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 1.34/1.52      inference('demod', [status(thm)], ['47', '63', '65', '66'])).
% 1.34/1.52  thf('68', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.34/1.52      inference('sup-', [status(thm)], ['44', '67'])).
% 1.34/1.52  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.34/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.34/1.52  thf('70', plain, ($false),
% 1.34/1.52      inference('demod', [status(thm)], ['43', '68', '69'])).
% 1.34/1.52  
% 1.34/1.52  % SZS output end Refutation
% 1.34/1.52  
% 1.35/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
