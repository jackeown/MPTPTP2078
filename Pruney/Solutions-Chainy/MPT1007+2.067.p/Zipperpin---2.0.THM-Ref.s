%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7glz6gBrif

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:24 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 391 expanded)
%              Number of leaves         :   53 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :  937 (4095 expanded)
%              Number of equality atoms :   93 ( 272 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v5_relat_1 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v5_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['5','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('17',plain,(
    v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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

thf('18',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ( X50
        = ( k1_relset_1 @ X50 @ X51 @ X52 ) )
      | ~ ( zip_tseitin_1 @ X52 @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X48: $i,X49: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( zip_tseitin_0 @ X53 @ X54 )
      | ( zip_tseitin_1 @ X55 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X40 @ X41 @ X39 )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['19','26','29'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ X35 ) )
      | ( ( k11_relat_1 @ X35 @ X34 )
        = ( k1_tarski @ ( k1_funct_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k11_relat_1 @ sk_C_2 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_C_2 @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_C_2 @ sk_A ) )
      | ( X0
        = ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( ( k11_relat_1 @ sk_C_2 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k11_relat_1 @ sk_C_2 @ sk_A ) )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','41'])).

thf('43',plain,
    ( ( k11_relat_1 @ sk_C_2 @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 != X17 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X17 ) )
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('45',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X17 ) )
     != ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X17 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    k1_xboole_0
 != ( k11_relat_1 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,
    ( ( sk_B @ ( k11_relat_1 @ sk_C_2 @ sk_A ) )
    = ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['42','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v4_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32
        = ( k7_relat_1 @ X32 @ X33 ) )
      | ~ ( v4_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2
      = ( k7_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('60',plain,
    ( sk_C_2
    = ( k7_relat_1 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['19','26','29'])).

thf('62',plain,
    ( sk_C_2
    = ( k7_relat_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) )
        = ( k9_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = ( k9_relat_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = ( k9_relat_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['19','26','29'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k11_relat_1 @ X22 @ X23 )
        = ( k9_relat_1 @ X22 @ ( k1_tarski @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k11_relat_1 @ sk_C_2 @ sk_A )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('72',plain,
    ( ( k11_relat_1 @ sk_C_2 @ sk_A )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['53','72'])).

thf('74',plain,(
    ~ ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['15','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = ( k9_relat_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['77'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('79',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( r1_tarski @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( ( k9_relat_1 @ X31 @ X30 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('83',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['19','26','29'])).

thf('85',plain,(
    ! [X17: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X17 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('86',plain,(
    k1_xboole_0
 != ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['83','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7glz6gBrif
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:46:30 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 270 iterations in 0.194s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.47/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.68  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.47/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.68  thf(t6_mcart_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68          ( ![B:$i]:
% 0.47/0.68            ( ~( ( r2_hidden @ B @ A ) & 
% 0.47/0.68                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.47/0.68                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.47/0.68                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.47/0.68                       ( r2_hidden @ G @ B ) ) =>
% 0.47/0.68                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      (![X42 : $i]:
% 0.47/0.68         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.47/0.68      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.47/0.68  thf(t61_funct_2, conjecture,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.68         ( m1_subset_1 @
% 0.47/0.68           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.68       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.68         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.68            ( m1_subset_1 @
% 0.47/0.68              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.68          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.68            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_2 @ 
% 0.47/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.68         ((v5_relat_1 @ X36 @ X38)
% 0.47/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('3', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 0.47/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.68  thf(d19_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X24 : $i, X25 : $i]:
% 0.47/0.68         (~ (v5_relat_1 @ X24 @ X25)
% 0.47/0.68          | (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.47/0.68          | ~ (v1_relat_1 @ X24))),
% 0.47/0.68      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_2 @ 
% 0.47/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc2_relat_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ A ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (![X20 : $i, X21 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.47/0.68          | (v1_relat_1 @ X20)
% 0.47/0.68          | ~ (v1_relat_1 @ X21))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.47/0.68        | (v1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.68  thf(fc6_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.68  thf('10', plain, ((v1_relat_1 @ sk_C_2)),
% 0.47/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.47/0.68      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.68  thf(d3_tarski, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.68          | (r2_hidden @ X0 @ X2)
% 0.47/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((r2_hidden @ X0 @ sk_B_1)
% 0.47/0.68          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.47/0.68        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_2)) @ sk_B_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['0', '13'])).
% 0.47/0.68  thf('15', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ sk_B_1)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X42 : $i]:
% 0.47/0.68         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.47/0.68      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.47/0.68  thf('17', plain, ((v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(d1_funct_2, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_1, axiom,
% 0.47/0.68    (![C:$i,B:$i,A:$i]:
% 0.47/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.47/0.68         (~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.47/0.68          | ((X50) = (k1_relset_1 @ X50 @ X51 @ X52))
% 0.47/0.68          | ~ (zip_tseitin_1 @ X52 @ X51 @ X50))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.47/0.68        | ((k1_tarski @ sk_A)
% 0.47/0.68            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_2)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.68  thf(zf_stmt_2, axiom,
% 0.47/0.68    (![B:$i,A:$i]:
% 0.47/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X48 : $i, X49 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ X48 @ X49) | ((X48) = (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_2 @ 
% 0.47/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.68  thf(zf_stmt_5, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.47/0.68         (~ (zip_tseitin_0 @ X53 @ X54)
% 0.47/0.68          | (zip_tseitin_1 @ X55 @ X53 @ X54)
% 0.47/0.68          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.47/0.68        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.68  thf('24', plain,
% 0.47/0.68      ((((sk_B_1) = (k1_xboole_0))
% 0.47/0.68        | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['20', '23'])).
% 0.47/0.68  thf('25', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('26', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.47/0.68  thf('27', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_2 @ 
% 0.47/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.47/0.68         (((k1_relset_1 @ X40 @ X41 @ X39) = (k1_relat_1 @ X39))
% 0.47/0.68          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.68  thf('29', plain,
% 0.47/0.68      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_2)
% 0.47/0.68         = (k1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.68  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('demod', [status(thm)], ['19', '26', '29'])).
% 0.47/0.68  thf(d1_tarski, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.47/0.68  thf('31', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.68         (((X12) != (X11))
% 0.47/0.68          | (r2_hidden @ X12 @ X13)
% 0.47/0.68          | ((X13) != (k1_tarski @ X11)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.47/0.68  thf('32', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_tarski @ X11))),
% 0.47/0.68      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.68  thf('33', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('sup+', [status(thm)], ['30', '32'])).
% 0.47/0.68  thf(t117_funct_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.68       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.68         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.68  thf('34', plain,
% 0.47/0.68      (![X34 : $i, X35 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X34 @ (k1_relat_1 @ X35))
% 0.47/0.68          | ((k11_relat_1 @ X35 @ X34) = (k1_tarski @ (k1_funct_1 @ X35 @ X34)))
% 0.47/0.68          | ~ (v1_funct_1 @ X35)
% 0.47/0.68          | ~ (v1_relat_1 @ X35))),
% 0.47/0.68      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.47/0.68  thf('35', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C_2)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C_2)
% 0.47/0.68        | ((k11_relat_1 @ sk_C_2 @ sk_A)
% 0.47/0.68            = (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.68  thf('36', plain, ((v1_relat_1 @ sk_C_2)),
% 0.47/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('37', plain, ((v1_funct_1 @ sk_C_2)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      (((k11_relat_1 @ sk_C_2 @ sk_A)
% 0.47/0.68         = (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X14 @ X13)
% 0.47/0.68          | ((X14) = (X11))
% 0.47/0.68          | ((X13) != (k1_tarski @ X11)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.47/0.68  thf('40', plain,
% 0.47/0.68      (![X11 : $i, X14 : $i]:
% 0.47/0.68         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['39'])).
% 0.47/0.68  thf('41', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X0 @ (k11_relat_1 @ sk_C_2 @ sk_A))
% 0.47/0.68          | ((X0) = (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['38', '40'])).
% 0.47/0.68  thf('42', plain,
% 0.47/0.68      ((((k11_relat_1 @ sk_C_2 @ sk_A) = (k1_xboole_0))
% 0.47/0.68        | ((sk_B @ (k11_relat_1 @ sk_C_2 @ sk_A))
% 0.47/0.68            = (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['16', '41'])).
% 0.47/0.68  thf('43', plain,
% 0.47/0.68      (((k11_relat_1 @ sk_C_2 @ sk_A)
% 0.47/0.68         = (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.47/0.68  thf(t20_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.47/0.68         ( k1_tarski @ A ) ) <=>
% 0.47/0.68       ( ( A ) != ( B ) ) ))).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (![X17 : $i, X18 : $i]:
% 0.47/0.68         (((X18) != (X17))
% 0.47/0.68          | ((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X17))
% 0.47/0.68              != (k1_tarski @ X18)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.47/0.68  thf('45', plain,
% 0.47/0.68      (![X17 : $i]:
% 0.47/0.68         ((k4_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X17))
% 0.47/0.68           != (k1_tarski @ X17))),
% 0.47/0.68      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.68  thf(t3_boole, axiom,
% 0.47/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.68  thf('46', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.68  thf(t48_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.68  thf('47', plain,
% 0.47/0.68      (![X9 : $i, X10 : $i]:
% 0.47/0.68         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.47/0.68           = (k3_xboole_0 @ X9 @ X10))),
% 0.47/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.68  thf('48', plain,
% 0.47/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['46', '47'])).
% 0.47/0.68  thf(t2_boole, axiom,
% 0.47/0.68    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.68  thf('49', plain,
% 0.47/0.68      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.68  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.68  thf('51', plain, (![X17 : $i]: ((k1_xboole_0) != (k1_tarski @ X17))),
% 0.47/0.68      inference('demod', [status(thm)], ['45', '50'])).
% 0.47/0.68  thf('52', plain, (((k1_xboole_0) != (k11_relat_1 @ sk_C_2 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['43', '51'])).
% 0.47/0.68  thf('53', plain,
% 0.47/0.68      (((sk_B @ (k11_relat_1 @ sk_C_2 @ sk_A)) = (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['42', '52'])).
% 0.47/0.68  thf('54', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_2 @ 
% 0.47/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('55', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X36 @ X37)
% 0.47/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('56', plain, ((v4_relat_1 @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.68  thf(t209_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.68       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.47/0.68  thf('57', plain,
% 0.47/0.68      (![X32 : $i, X33 : $i]:
% 0.47/0.68         (((X32) = (k7_relat_1 @ X32 @ X33))
% 0.47/0.68          | ~ (v4_relat_1 @ X32 @ X33)
% 0.47/0.68          | ~ (v1_relat_1 @ X32))),
% 0.47/0.68      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.47/0.68  thf('58', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C_2)
% 0.47/0.68        | ((sk_C_2) = (k7_relat_1 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.68  thf('59', plain, ((v1_relat_1 @ sk_C_2)),
% 0.47/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('60', plain, (((sk_C_2) = (k7_relat_1 @ sk_C_2 @ (k1_tarski @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['58', '59'])).
% 0.47/0.68  thf('61', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('demod', [status(thm)], ['19', '26', '29'])).
% 0.47/0.68  thf('62', plain,
% 0.47/0.68      (((sk_C_2) = (k7_relat_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))),
% 0.47/0.68      inference('demod', [status(thm)], ['60', '61'])).
% 0.47/0.68  thf(t148_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.47/0.68  thf('63', plain,
% 0.47/0.68      (![X28 : $i, X29 : $i]:
% 0.47/0.68         (((k2_relat_1 @ (k7_relat_1 @ X28 @ X29)) = (k9_relat_1 @ X28 @ X29))
% 0.47/0.68          | ~ (v1_relat_1 @ X28))),
% 0.47/0.68      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.68  thf('64', plain,
% 0.47/0.68      ((((k2_relat_1 @ sk_C_2) = (k9_relat_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('sup+', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('65', plain, ((v1_relat_1 @ sk_C_2)),
% 0.47/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('66', plain,
% 0.47/0.68      (((k2_relat_1 @ sk_C_2) = (k9_relat_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))),
% 0.47/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.68  thf('67', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('demod', [status(thm)], ['19', '26', '29'])).
% 0.47/0.68  thf(d16_relat_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ A ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.47/0.68  thf('68', plain,
% 0.47/0.68      (![X22 : $i, X23 : $i]:
% 0.47/0.68         (((k11_relat_1 @ X22 @ X23) = (k9_relat_1 @ X22 @ (k1_tarski @ X23)))
% 0.47/0.68          | ~ (v1_relat_1 @ X22))),
% 0.47/0.68      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.47/0.68  thf('69', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k11_relat_1 @ X0 @ sk_A)
% 0.47/0.68            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C_2)))
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['67', '68'])).
% 0.47/0.68  thf('70', plain,
% 0.47/0.68      ((((k11_relat_1 @ sk_C_2 @ sk_A) = (k2_relat_1 @ sk_C_2))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('sup+', [status(thm)], ['66', '69'])).
% 0.47/0.68  thf('71', plain, ((v1_relat_1 @ sk_C_2)),
% 0.47/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('72', plain, (((k11_relat_1 @ sk_C_2 @ sk_A) = (k2_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('demod', [status(thm)], ['70', '71'])).
% 0.47/0.68  thf('73', plain,
% 0.47/0.68      (((sk_B @ (k2_relat_1 @ sk_C_2)) = (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['53', '72'])).
% 0.47/0.68  thf('74', plain, (~ (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_2)) @ sk_B_1)),
% 0.47/0.68      inference('demod', [status(thm)], ['15', '73'])).
% 0.47/0.68  thf('75', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['14', '74'])).
% 0.47/0.68  thf('76', plain,
% 0.47/0.68      (((k2_relat_1 @ sk_C_2) = (k9_relat_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))),
% 0.47/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.68  thf(d10_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.68  thf('77', plain,
% 0.47/0.68      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.68  thf('78', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.47/0.68      inference('simplify', [status(thm)], ['77'])).
% 0.47/0.68  thf(t152_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.47/0.68            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.47/0.68  thf('79', plain,
% 0.47/0.68      (![X30 : $i, X31 : $i]:
% 0.47/0.68         (((X30) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X31)
% 0.47/0.68          | ~ (r1_tarski @ X30 @ (k1_relat_1 @ X31))
% 0.47/0.68          | ((k9_relat_1 @ X31 @ X30) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.47/0.68  thf('80', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) != (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.68  thf('81', plain,
% 0.47/0.68      ((((k2_relat_1 @ sk_C_2) != (k1_xboole_0))
% 0.47/0.68        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('sup-', [status(thm)], ['76', '80'])).
% 0.47/0.68  thf('82', plain, ((v1_relat_1 @ sk_C_2)),
% 0.47/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('83', plain,
% 0.47/0.68      ((((k2_relat_1 @ sk_C_2) != (k1_xboole_0))
% 0.47/0.68        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('84', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('demod', [status(thm)], ['19', '26', '29'])).
% 0.47/0.68  thf('85', plain, (![X17 : $i]: ((k1_xboole_0) != (k1_tarski @ X17))),
% 0.47/0.68      inference('demod', [status(thm)], ['45', '50'])).
% 0.47/0.68  thf('86', plain, (((k1_xboole_0) != (k1_relat_1 @ sk_C_2))),
% 0.47/0.68      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.68  thf('87', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['83', '86'])).
% 0.47/0.68  thf('88', plain, ($false),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['75', '87'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
